(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_parser

open Util
module F = Ast.Func
module R = Runtime_trace_off
module D = Data

exception CompileError of Loc.t option * string

let error ?loc msg = raise (CompileError(loc,msg))

type flags = {
  defined_variables : StrSet.t;
  print_passes : bool;
  print_units : bool;
}
[@@deriving show]

let default_flags = {
  defined_variables = StrSet.empty;
  print_passes = false;
  print_units = false;
}

let parser : (module Parse.Parser) option D.State.component = D.State.declare
  ~descriptor:D.elpi_state_descriptor
  ~name:"elpi:parser"
  ~pp:(fun fmt _ -> Format.fprintf fmt "<parser>")
  ~clause_compilation_is_over:(fun x -> x)
  ~goal_compilation_begins:(fun x -> x)
  ~goal_compilation_is_over:(fun ~args:_ x -> Some x)
  ~compilation_is_over:(fun x -> Some x)
  ~execution_is_over:(fun _ -> None)
  ~init:(fun () -> None)

let filter1_if { defined_variables } proj c =
  match proj c with
  | None -> true
  | Some e when StrSet.mem e defined_variables -> true
  | Some _ -> false

let filter_if flags proj l =
  List.filter (filter1_if flags proj) l


(* Symbol table of a compilation unit (part of the compiler state).

   The initial value is taken from Data.Global_symbols, then both global
   names and local ones are allocated (hashconsed) in this table.

   Given a two symbols table (base and second) we can obtain a new one
   (updated base) via [build_shift] that contains the union of the symbols
   and a relocation to be applied to a program that lives in the second table.
   The code applying the shift is also supposed to re-hashcons and recognize
   builtins.
*)

module SymbolMap : sig
  type table
  val pp_table : Format.formatter -> table -> unit

  val empty : unit -> table
  val allocate_global_symbol     : D.State.t -> table -> F.t -> table * (D.constant * D.term)
  val allocate_bound_symbol      : D.State.t -> table -> F.t -> D.constant -> table * D.term
  val get_canonical              : D.State.t -> table -> D.constant -> D.term
  val global_name : D.State.t -> table -> D.constant -> F.t
  val compile : table -> D.symbol_table

end = struct

  type table = {
    ast2ct : (D.constant * D.term) F.Map.t;
    c2t : (F.t * D.term) D.Constants.Map.t;
    last_global : int;
  }
  [@@deriving show]

  let compile { last_global; c2t; ast2ct } =
    let t = { D.c2s = Hashtbl.create 37; c2t = Hashtbl.create 37; frozen_constants = last_global; } in
    F.Map.iter (fun k (c,v) -> Hashtbl.add t.c2t c v; Hashtbl.add t.c2s c (F.show k)) ast2ct;
    t
    

  let empty () =
    if not @@ D.Global_symbols.table.locked then
      anomaly "SymbolMap created before Global_symbols.table is locked";
  {
    ast2ct = D.Global_symbols.(table.s2ct);
    last_global = D.Global_symbols.table.last_global;
    c2t = D.Global_symbols.(table.c2s);
  }

  let allocate_global_symbol_aux x ({ c2t; ast2ct; last_global } as table) =
    try table, F.Map.find x ast2ct
    with Not_found ->
      let last_global = last_global - 1 in
      let n = last_global in
      let xx = D.Term.Const n in
      let p = n,xx in
      let c2t = D.Constants.Map.add n (x,xx) c2t in
      let ast2ct = F.Map.add x p ast2ct in
      { c2t; ast2ct; last_global }, p

  let allocate_global_symbol state table x =
    if not (D.State.get D.while_compiling state) then
      anomaly ("global symbols can only be allocated during compilation");
    allocate_global_symbol_aux x table

  let allocate_bound_symbol_aux f n ({ c2t; ast2ct } as table) =
    try table, snd @@ D.Constants.Map.find n c2t
    with Not_found ->
      let xx = D.Term.Const n in
      let c2t = D.Constants.Map.add n (f,xx) c2t in (* TODO: f makes no sense here, use c0 ... cn *)
      { table with c2t; ast2ct }, xx

  let allocate_bound_symbol state table f n =
    if not (D.State.get D.while_compiling state) then
      anomaly "bound symbols can only be allocated during compilation";
    if n < 0 then
      anomaly "bound variables are positive";
    allocate_bound_symbol_aux f n table
  ;;

  let get_canonical state table c =
    if not (D.State.get D.while_compiling state) then
      anomaly "get_canonical can only be used during compilation";
    try snd @@ D.Constants.Map.find c table.c2t
    with Not_found -> anomaly ("unknown symbol " ^ string_of_int c)

  let global_name state table c =
    if not (D.State.get D.while_compiling state) then
      anomaly "get_canonical can only be used during compilation";
    try fst @@ D.Constants.Map.find c table.c2t
    with Not_found -> anomaly ("unknown symbol " ^ string_of_int c)

end
(* 
module Symbols : sig

  (* Compilation phase *)
  val allocate_global_symbol     : D.State.t -> F.t -> D.State.t * (D.constant * D.term)
  val allocate_global_symbol_str : D.State.t -> string -> D.State.t * D.constant
  val allocate_Arg_symbol        : D.State.t -> int -> D.State.t * D.constant
  val allocate_bound_symbol      : D.State.t -> int -> D.State.t * D.term
  val get_global_or_allocate_bound_symbol : D.State.t -> int -> D.State.t * D.term
  val get_canonical              : D.State.t -> int -> D.term
  val get_global_symbol          : D.State.t -> F.t -> D.constant * D.term
  val get_global_symbol_str      : D.State.t -> string -> D.constant * D.term
  val show                       : D.State.t -> D.constant -> string

  type table
  type pruned_table
  val pp_table : Format.formatter -> table -> unit
  val pp_pruned_table : Format.formatter -> pruned_table -> unit
  val table : table D.State.component
  val compile_table : table -> D.symbol_table
  val lock : table -> table
  val locked : table -> bool
  val equal : table -> table -> bool
  val size : pruned_table -> int
  val prune : table -> alive:D.Constants.Set.t -> pruned_table
  (* debug *)
  val symbols : pruned_table -> string list

  val global_table : unit -> table
  val uuid : table -> UUID.t

  val build_shift : ?lock_base:bool -> flags:flags -> base:D.State.t -> pruned_table -> (D.State.t * D.constant D.Constants.Map.t, string) Stdlib.Result.t

end = struct

(* The table is locked at runtime, but also after a program is compiled.
   All units subsequently compiled can inherit the locked symbol table.
   It is temporary unlocked to compile the query.
*)
type table = {
  ast2ct : (D.constant * D.term) F.Map.t;
  c2s : string D.Constants.Map.t;
  c2t : D.term D.Constants.Map.t;
  last_global : int;
  locked : bool; (* prevents new allocation *)
  frozen : bool;
  uuid : Util.UUID.t;
} [@@deriving show]

type entry =
| GlobalSymbol of D.constant * string
| BoundVariable of D.constant * D.term
[@@deriving show]

type pruned_table = entry array [@@deriving show]

let locked { locked } = locked
let lock t = { t with locked = true }
let uuid { uuid } = uuid
let equal t1 t2 =
  locked t1 && locked t2 && uuid t1 = uuid t2

let size t = Array.length t

let symbols table =
  let map = function
  | GlobalSymbol (c, s) -> Some (s ^ ":" ^ string_of_int c)
  | BoundVariable _ -> None
  in
  List.rev @@ List.filter_map map @@ Array.to_list table

let prune t ~alive =
  let c2s = t.c2s in
  let c2t0 = D.Constants.Map.filter (fun k _ -> D.Constants.Set.mem k alive) t.c2t in
  let map k t =
    if k < 0 then GlobalSymbol (k, D.Constants.Map.find k c2s)
    else BoundVariable (k, t)
  in
  let c2t0 = D.Constants.Map.mapi map c2t0 in
  Array.of_list @@ List.rev_map snd @@ D.Constants.Map.bindings c2t0

let table = D.State.declare
  ~descriptor:D.elpi_state_descriptor
  ~name:"elpi:compiler:symbol_table"
  ~pp:pp_table
  ~clause_compilation_is_over:(fun x -> x)
  ~goal_compilation_begins:(fun x -> x)
  ~goal_compilation_is_over:(fun ~args:_ x -> Some x)
  ~compilation_is_over:(fun x -> Some { x with frozen = true }) (* to implement read_term and relocate_closed_term *)
  ~execution_is_over:(fun _ -> None)
  ~init:(fun () -> {
    ast2ct = F.Map.empty;
    last_global = D.Global_symbols.table.last_global;
    c2s = D.Constants.Map.empty;
    c2t = D.Constants.Map.empty;
    locked = false;
    uuid = Util.UUID.make ();
    frozen = false;
  })

(* let global_table () =
  {
    ast2ct = StrMap.fold (fun s v m -> F.Map.add (F.from_string s) v m) D.Global_symbols.table.s2ct F.Map.empty;
    c2t = D.Constants.Map.map (fun x -> snd @@ StrMap.find x D.Global_symbols.table.s2ct) D.Global_symbols.table.c2s;
    c2s = D.Global_symbols.table.c2s;
    last_global = D.Global_symbols.table.last_global;
    locked = false;
    uuid = Util.UUID.make ();
    frozen = false;
  } *)

let compile_table t =
  let c2s = Hashtbl.create 37 in
  D.Constants.Map.iter (Hashtbl.add c2s) t.c2s;
  let c2t = Hashtbl.create 37 in
  D.Constants.Map.iter (Hashtbl.add c2t) t.c2t;
  {
    D.c2s;
    c2t;
    frozen_constants = t.last_global;
  }

let allocate_global_symbol_aux x ({ c2s; c2t; ast2ct; last_global; locked; frozen; uuid } as table) =
  try table, F.Map.find x ast2ct
  with Not_found ->
    if frozen then
      error ("allocating new global symbol '"^F.show x^"' at runtime");
    if locked then
      error ("allocating new global symbol '"^F.show x^"' since the symbol table is locked");
    let last_global = last_global - 1 in
    let n = last_global in
    let xx = D.Term.Const n in
    let p = n,xx in
    let c2s = D.Constants.Map.add n (F.show x) c2s in
    let c2t = D.Constants.Map.add n xx c2t in
    let ast2ct = F.Map.add x p ast2ct in
    { c2s; c2t; ast2ct; last_global; locked; frozen; uuid }, p

let allocate_global_symbol state x =
  if not (D.State.get D.while_compiling state) then
    anomaly ("global symbols can only be allocated during compilation");
  D.State.update_return table state (allocate_global_symbol_aux x)

let allocate_global_symbol_str st x =
  let x = F.from_string x in
  let st, (c,_) = allocate_global_symbol st x in
  st, c

let allocate_Arg_symbol st n =
  let x = Printf.sprintf "%%Arg%d" n in
  allocate_global_symbol_str st x

let show state n =
  try D.Constants.Map.find n (D.State.get table state).c2s
  with Not_found ->
    if n >= 0 then "c" ^ string_of_int n
    else "SYMBOL" ^ string_of_int n

let allocate_bound_symbol_aux n ({ c2s; c2t; ast2ct; last_global; locked; frozen; uuid } as table) =
  try table, D.Constants.Map.find n c2t
  with Not_found ->
    if frozen then
      error ("allocating new bound symbol 'c"^string_of_int n^"' at runtime");
    let xx = D.Term.Const n in
    let c2t = D.Constants.Map.add n xx c2t in
    { c2s; c2t; ast2ct; last_global; locked; frozen; uuid }, xx

let allocate_bound_symbol state n =
  if not (D.State.get D.while_compiling state) then
    anomaly "bound symbols can only be allocated during compilation";
  if n < 0 then
    anomaly "bound variables are positive";
  D.State.update_return table state (allocate_bound_symbol_aux n)
;;

let get_canonical state c =
  if not (D.State.get D.while_compiling state) then
    anomaly "get_canonical can only be used during compilation";
  try D.Constants.Map.find c (D.State.get table state).c2t
  with Not_found -> anomaly ("unknown symbol " ^ string_of_int c)

let get_global_or_allocate_bound_symbol state n =
  if n >= 0 then allocate_bound_symbol state n
  else state, get_canonical state n

let get_global_symbol state s =
  if not (D.State.get D.while_compiling state) then
    anomaly "get_global_symbol can only be used during compilation";
  try F.Map.find s (D.State.get table state).ast2ct
  with Not_found -> anomaly ("unknown symbol " ^ F.show s)

let get_global_symbol_str state s = get_global_symbol state (F.from_string s)

exception Cannot_build_shift of string

let build_shift ?(lock_base=false) ~flags:{ print_units } ~base symbols =
  let open D.Constants in
  D.State.update_return table base (fun base ->
    (* We try hard to respect the same order if possible, since some tests
       (grundlagen) depend on this order (for performance, the constant-timestamp
       heuristic in unfolding) *)
    Array.fold_left (fun (base,shift as acc) e ->
      match e with
      | GlobalSymbol (v, name) ->
        begin try
          let c, _ = F.Map.find (F.from_string name)  base.ast2ct in
          if c == v then acc
          else begin
            if print_units then Printf.printf "Relocate: %d -> %d (%s)\n%!" v c name;
            base, Map.add v c shift
          end
        with
        | Not_found when lock_base -> raise (Cannot_build_shift (name))
        | Not_found ->
          let base, (c,_) = allocate_global_symbol_aux (Ast.Func.from_string name) base in
          base, Map.add v c shift
        end
      | BoundVariable (v, t) ->
        if Map.mem v base.c2t then acc
        else
          let base = { base with c2t = Map.add v t base.c2t } in
          base, shift
      )
     (base, Map.empty) symbols)

let build_shift ?lock_base ~flags ~base symbols =
  try Stdlib.Result.Ok (build_shift ?lock_base ~flags ~base symbols)
  with Cannot_build_shift s -> Stdlib.Result.Error s

end *)


module Builtins : sig

  val all : D.State.t -> D.Constants.Set.t
  val register : D.State.t -> D.BuiltInPredicate.t -> D.constant -> D.State.t
  val is_declared : D.State.t -> D.constant -> bool
  (* val is_declared_str : D.State.t -> string -> bool *)

  type t = {
    names : StrSet.t;
    constants : D.Constants.Set.t;
    code : D.BuiltInPredicate.t list;
  }
  val is_empty : t -> bool
  val empty : t
  val builtins : t D.State.component
  val equal : t -> t -> bool

end = struct

  type t = {
    names : StrSet.t;
    constants : D.Constants.Set.t;
    code : D.BuiltInPredicate.t list;
  }

  let equal t1 t2 =
    StrSet.equal t1.names t2.names &&
    D.Constants.Set.equal t1.constants t2.constants

let is_empty { names } = StrSet.is_empty names
let empty =  { names = StrSet.empty; constants = D.Constants.Set.empty; code = [] }

let builtins : t D.State.component = D.State.declare
  ~descriptor:D.elpi_state_descriptor
  ~name:"elpi:compiler:builtins"
  ~pp:(fun fmt x -> StrSet.pp fmt x.names)
  ~init:(fun () -> empty)
  ~clause_compilation_is_over:(fun x -> x)
  ~goal_compilation_begins:(fun x -> x)
  ~goal_compilation_is_over:(fun ~args x -> Some x)
  ~compilation_is_over:(fun x -> Some x) (* to implement read_term *)
  ~execution_is_over:(fun _ -> None)
;;

let all state = (D.State.get builtins state).constants

let register state (D.BuiltInPredicate.Pred(s,_,_) as b) idx =
  if s = "" then anomaly "Built-in predicate name must be non empty";
  if not (D.State.get D.while_compiling state) then
    anomaly "Built-in can only be declared at compile time";
  let declared = (D.State.get builtins state).constants in
  if D.Constants.Set.mem idx declared then
    anomaly ("Duplicate built-in predicate " ^ s);
  D.State.update builtins state (fun { names; constants; code } ->
    { names = StrSet.add s names;
      constants = D.Constants.Set.add idx constants;
      code = b :: code;
    })
;;

let is_declared state x =
  let declared = (D.State.get builtins state).constants in
  D.Constants.Set.mem x declared
  || x == D.Global_symbols.declare_constraintc
  || x == D.Global_symbols.print_constraintsc
  || x == D.Global_symbols.cutc
  || x == D.Global_symbols.eqc
  || x == D.Global_symbols.findall_solutionsc
;;

(* let is_declared state x =
  let declared = (D.State.get builtins state).constants in
  D.Constants.Set.mem x declared
  || x == D.Global_symbols.declare_constraintc
  || x == D.Global_symbols.print_constraintsc
  || x == D.Global_symbols.cutc
  || x == D.Global_symbols.eqc
  || x == D.Global_symbols.findall_solutionsc *)
;;

end

(****************************************************************************
  Data types
 ****************************************************************************)

(* This is paired with a pre-stack term, i.e. a stack term where args are
 * represented with constants as "%Arg3" *)
type argmap = {
  nargs : int;
  c2i : int D.Constants.Map.t;
  i2n : string IntMap.t;
  n2t : (D.term * D.Constants.t) StrMap.t;
  n2i : int StrMap.t;
}
[@@ deriving show, ord]

let empty_amap = {
 nargs = 0;
 c2i = D.Constants.Map.empty;
 i2n = IntMap.empty;
 n2t = StrMap.empty;
 n2i = StrMap.empty;
}

let is_empty_amap { c2i; nargs; i2n; n2t; n2i } =
  nargs = 0 &&
  IntMap.is_empty i2n &&
  StrMap.is_empty n2t &&
  StrMap.is_empty n2i

(* let raw_mk_Arg s n  { c2i; nargs; i2n; n2t; n2i } =
  let s, nc = Symbols.allocate_Arg_symbol s nargs in
  let n' = Symbols.get_canonical s nc in
  let i2n = IntMap.add nargs n i2n in
  let c2i = D.Constants.Map.add nc nargs c2i in
  let n2t = StrMap.add n (n',nc) n2t in
  let n2i = StrMap.add n nargs n2i in
  let nargs = nargs + 1 in
  s, { c2i; nargs; i2n; n2t; n2i }, (n', nc) *)

(* type preterm = {
  term : D.term; (* Args are still constants *)
  amap : argmap;
  loc : Loc.t;
  spilling : bool;
}
[@@ deriving show, ord]

type pretype = {
  ttype : D.ttype; (* Args are still constants *)
  tamap : argmap;
  tloc : Loc.t;
}
[@@ deriving show, ord]

type type_declaration = {
  tname : D.constant;
  ttype : pretype;
  tloc : Loc.t;
}
[@@ deriving show, ord]

type type_abbrev_declaration = {
  taname : D.constant;
  tavalue : pretype;
  taparams : int;
  taloc : Loc.t;
  timestamp:int
}
[@@ deriving show, ord]

type presequent = {
  peigen : D.term;
  pcontext : D.term;
  pconclusion : D.term;
}
[@@ deriving show, ord]
type prechr_rule = {
  pto_match : presequent list;
  pto_remove : presequent list;
  pguard : D.term option;
  pnew_goal : presequent option;
  pamap : argmap;
  pname : string;
  pifexpr : string option;
  pcloc : Loc.t;
}
[@@ deriving show, ord] *)

(****************************************************************************
  Intermediate program representation
 ****************************************************************************)

open Data
module C = Constants

(* type block_constraint = {
   clique : constant list;
   ctx_filter : constant list;
   rules : prechr_rule list
}
[@@deriving show, ord] *)

module ScopeContext = struct

  type scope = Local | Global
  [@@ deriving show, ord]

type ctx = { vmap : (F.t * F.t) list; uvmap : (F.t * F.t) list ref }
let empty () = { vmap = []; uvmap = ref [] }

let eq_var { vmap } c1 c2 = List.mem (c1,c2) vmap


let purge f c l = List.filter (fun x -> not @@ F.equal (f x) c) l
let push_ctx c1 c2 ctx = { ctx with vmap = (c1 , c2) :: (purge fst c1 @@ purge snd c2 ctx.vmap) }
let eq_uvar ctx c1 c2 =
  if List.exists (fun (x,_) -> F.equal x c1) !(ctx.uvmap) ||
     List.exists (fun (_,y) -> F.equal y c2) !(ctx.uvmap) then
    List.mem (c1,c2) !(ctx.uvmap)
  else begin
    ctx.uvmap := (c1,c2) :: !(ctx.uvmap);
    true
  end
end

module Arity = struct type t = int * Loc.t [@@deriving show, ord] end

module ScopedTypeExpression = struct
  open ScopeContext
  type t_ =
    | Prop | Any
    | Const of scope * F.t
    | App of F.t * e * e list
    | Arrow of Ast.Structured.variadic * e * e
    | Pred of Ast.Structured.functionality * (Ast.Mode.t * e) list
  and e = { it : t_; loc : Loc.t }
  [@@ deriving show]

  type v_ =
    | Lam of F.t * v_
    | Ty of e
  [@@ deriving show]

  type t = { name : F.t; value : v_; nparams : int; loc : Loc.t; indexing : Ast.Structured.tattribute option }
  [@@ deriving show]

  let rec eqt ctx t1 t2 =
    match t1.it, t2.it with
    | Const(Global,c1), Const(Global,c2) -> F.equal c1 c2
    | Const(Local,c1), Const(Local,c2) -> eq_var ctx c1 c2
    | App(c1,x,xs), App(c2,y,ys) -> F.equal c1 c2 && eqt ctx x y && Util.for_all2 (eqt ctx) xs ys
    | Arrow(b1,s1,t1), Arrow(b2,s2,t2) -> b1 == b2 && eqt ctx s1 s2 && eqt ctx t1 t2
    | Pred(f1,l1), Pred(f2,l2) -> f1 == f2 && Util.for_all2 (fun (m1,t1) (m2,t2) -> Ast.Mode.compare m1 m2 == 0 && eqt ctx t1 t2) l1 l2
    | Prop, Prop -> true
    | Any, Any -> true
    | _ -> false

  let rec eq ctx t1 t2 =
    match t1, t2 with
    | Lam(c1,b1), Lam(c2,b2) -> eq (push_ctx c1 c2 ctx) b1 b2
    | Ty t1, Ty t2 -> eqt ctx t1 t2
    | _ -> false

  let equal { name = n1; value = x } { name = n2; value = y } = F.equal n1 n2 && eq (empty ()) x y

  let compare _ _ = assert false

  let rec smart_map_scoped_loc_ty f ({ it; loc } as orig) =
    let it' = smart_map_scoped_ty f it in
    if it' == it then orig else { it = it'; loc }
  and smart_map_scoped_ty f orig =
    match orig with
    | Prop -> orig
    | Any -> orig
    | Const(ScopeContext.Local,_) -> orig
    | Const(ScopeContext.Global,c) ->
        let c' = f c in
        if c == c' then orig else Const(ScopeContext.Global,c')
    | App(c,x,xs) ->
        let c' = f c in
        let x' = smart_map_scoped_loc_ty f x in
        let xs' = smart_map (smart_map_scoped_loc_ty f) xs in
        if c' == c && x' == x && xs' == xs then orig else App(c',x',xs')
    | Arrow(v,x,y) ->
        let x' = smart_map_scoped_loc_ty f x in
        let y' = smart_map_scoped_loc_ty f y in
        if x' == x && y' == y then orig else Arrow(v,x',y')
    | Pred(c,l) ->
        let l' = smart_map (fun (m,x as orig) ->
          let x' = smart_map_scoped_loc_ty f x in
          if x' == x then orig else m,x') l in
        if l' == l then orig else Pred(c,l')

  let rec smart_map_tye f = function
    | Lam(c,t) as orig ->
        let t' = smart_map_tye f t in
        if t == t' then orig else Lam(c,t')
    | Ty t as orig ->
      let t' = smart_map_scoped_loc_ty f t in
      if t == t' then orig else Ty t'

  let smart_map f ({ name; value; nparams; loc; indexing } as orig) =
    let name' = f name in
    let value' = smart_map_tye f value in
    if name == name' && value' == value then orig
    else { name = name'; value = value'; nparams; loc; indexing }

end

module MutableOnce : sig 
  type 'a t
  [@@ deriving show]
  val make : F.t -> 'a t
  val create : 'a -> 'a t
  val set : 'a t -> 'a -> unit
  val unset : 'a t -> unit
  val get : 'a t -> 'a
  val is_set : 'a t -> bool
  val pretty : Format.formatter -> 'a t -> unit
end = struct
  type 'a t = F.t * 'a option ref
  [@@ deriving show]

  let make f = f, ref None

  let create t = F.from_string "_", ref (Some t)

  let is_set (_,x) = Option.is_some !x
  let set (_,r) x =
    match !r with
    | None -> r := Some x
    | Some _ -> anomaly "MutableOnce"
  
  let get (_,x) = match !x with Some x -> x | None -> anomaly "get"
  let unset (_,x) = x := None

  let pretty fmt (f,x) =
    match !x with
    | None -> Format.fprintf fmt "%a" F.pp f
    | Some _ -> anomaly "pp"
end

module TypeAssignment = struct

  type 'a overloading =
    | Single of 'a
    | Overloaded of 'a list
  [@@ deriving show, fold]

  type 'a t_ =
    | Prop | Any
    | Cons of F.t
    | App of F.t * 'a t_ * 'a t_ list
    | Arr of Ast.Structured.variadic * 'a t_ * 'a t_
    | UVar of 'a
  [@@ deriving show, fold]

  type skema = Lam of F.t * skema | Ty of F.t t_
  [@@ deriving show]
  type overloaded_skema = skema overloading
  [@@ deriving show]

  type t = Val of t MutableOnce.t t_
  [@@ deriving show]

  let nparams t =
      let rec aux = function Ty _ -> 0 | Lam(_,t) -> 1 + aux t in
      aux t
  
  let rec subst map = function
    | (Prop | Any | Cons _) as x -> x
    | UVar c -> F.Map.find c map
    | App(c,x,xs) -> App (c,subst map x,List.map (subst map) xs)
    | Arr(v,s,t) -> Arr(v,subst map s, subst map t)

  let fresh sk =
    let rec fresh map = function
      | Lam(c,t) -> fresh (F.Map.add c (UVar (MutableOnce.make c)) map) t
      | Ty t -> if F.Map.is_empty map then Obj.magic t, map else subst map t, map
  in
    fresh F.Map.empty sk

  let fresh_overloaded = function
    | Single sk -> Single (fst @@ fresh sk)
    | Overloaded l -> Overloaded (List.map (fun x -> fst @@ fresh x) l)

  let rec apply m sk args =
    match sk, args with
    | Ty t, [] -> if F.Map.is_empty m then Obj.magic t else subst m t
    | Lam(c,t), x::xs -> apply (F.Map.add c x m) t xs
    | _ -> assert false (* kind checker *)

  let apply sk args = apply F.Map.empty sk args

  let merge_skema x y =
    match x, y with
    | Single x, Single y -> Overloaded [x;y]
    | Single x, Overloaded ys -> Overloaded (x::ys)
    | Overloaded xs, Single y -> Overloaded(xs@[y])
    | Overloaded xs, Overloaded ys -> Overloaded (xs @ ys)
  
  let unval (Val x) = x
  let deref m = unval @@ MutableOnce.get m
  let set m v = MutableOnce.set m (Val v)


  open Format

  let rec pretty fmt = function
    | Prop -> fprintf fmt "prop"
    | Any -> fprintf fmt "any"
    | Cons c -> F.pp fmt c
    | App(f,x,xs) -> fprintf fmt "%a %a" F.pp f (Util.pplist pretty " ") (x::xs)
    | Arr(Ast.Structured.NotVariadic,s,t) -> fprintf fmt "%a -> %a" pretty s pretty t
    | Arr(Ast.Structured.Variadic,s,t) -> fprintf fmt "%a ..-> %a" pretty s pretty t
    | UVar m when MutableOnce.is_set m -> pretty fmt @@ deref m
    | UVar m -> MutableOnce.pretty fmt m

  let vars_of (Val t)  = fold_t_ (fun xs x -> if MutableOnce.is_set x then xs else x :: xs) [] t

end
module ScopedTerm = struct
  open ScopeContext

  type t_ =
   | Const of scope * F.t
   | Discard
   | Var of F.t * t list
   | App of scope * F.t * t * t list
   | Lam of F.t option * t
   | CData of CData.t
   | Spill of t * int (* 0 is the original, 1.. its phantoms *)
   and t = { it : t_; loc : Loc.t; ty : TypeAssignment.t MutableOnce.t }
  [@@ deriving show]

  let type_of { ty } = assert(MutableOnce.is_set ty); TypeAssignment.deref ty

  open Format
  let rec pretty fmt { it } = pretty_ fmt it
  and pretty_ fmt = function
    | Const(_,f) -> fprintf fmt "%a" F.pp f
    | Discard -> fprintf fmt "_"
    | Lam(None,t) -> fprintf fmt "_\\ %a" pretty t
    | Lam(Some f,t) -> fprintf fmt "%a\\ %a" F.pp f pretty t
    | App(Global,f,x,[]) when F.equal F.spillf f -> fprintf fmt "{%a}" pretty x
    | App(_,f,x,xs) -> fprintf fmt "(%a %a)" F.pp f (Util.pplist pretty " ") (x::xs)
    | Var(f,xs) -> fprintf fmt "(%a %a)" F.pp f (Util.pplist pretty " ") xs
    | CData c -> fprintf fmt "%a" CData.pp c
    | Spill (t,0) -> fprintf fmt "{%a}" pretty t
    | Spill (t,n) -> fprintf fmt "{%a}_%d" pretty t n
    

  let equal t1 t2 =
    let rec eq ctx t1 t2 =
      match t1.it, t2.it with
      | Const(Global,c1), Const(Global,c2) -> F.equal c1 c2
      | Const(Local,c1), Const(Local,c2) -> eq_var ctx c1 c2
      | Discard, Discard -> true
      | Var(n1,l1), Var(n2,l2) -> eq_uvar ctx n1 n2 && Util.for_all2 (eq ctx) l1 l2
      | App(Global,c1,x,xs), App(Global,c2,y,ys) -> F.equal c1 c2 && eq ctx x y && Util.for_all2 (eq ctx) xs ys
      | App(Local,c1,x,xs), App(Local,c2,y,ys) -> eq_var ctx c1 c2 && eq ctx x y && Util.for_all2 (eq ctx) xs ys
      | Lam(None,b1), Lam (None, b2) -> eq ctx b1 b2
      | Spill(b1,n1), Spill (b2,n2) -> n1 == n2 && eq ctx b1 b2
      | Lam(Some c1,b1), Lam(Some c2, b2) -> eq (push_ctx c1 c2 ctx) b1 b2
      | CData c1, CData c2 -> CData.equal c1 c2
      | _ -> false
    in
      eq (empty ()) t1 t2

    let compare _ _ = assert false

end


module TypeList = struct

  type t = ScopedTypeExpression.t list
  [@@deriving show, ord]
  
  let make t = [t]
    
  let smart_map = smart_map
  
  let append x t = if List.exists (ScopedTypeExpression.equal x) t then t else x :: t
  let merge t1 t2 = List.fold_left (fun acc x -> append x acc) t1 t2

  let fold = List.fold_left
  
end
  
module TypeChecker : sig

  type type_abbrevs = TypeAssignment.skema F.Map.t
  type arities = Arity.t F.Map.t
  val check_disjoint : type_abbrevs:ScopedTypeExpression.t F.Map.t -> kinds:arities -> unit

  val check_type : type_abbrevs:type_abbrevs -> arities -> ScopedTypeExpression.t -> TypeAssignment.skema
  val check_types : type_abbrevs:type_abbrevs -> arities -> TypeList.t -> TypeAssignment.overloaded_skema

  type env = TypeAssignment.overloaded_skema F.Map.t
  val check : type_abbrevs:type_abbrevs-> kinds:arities -> env:env -> ScopedTerm.t -> exp:TypeAssignment.t -> bool

end = struct
  type type_abbrevs = TypeAssignment.skema F.Map.t
  type arities = Arity.t F.Map.t

  let check_disjoint ~type_abbrevs ~kinds =
    kinds |> F.Map.iter (fun k (_,lock) -> if F.Map.mem k type_abbrevs then
      let { ScopedTypeExpression.loc } = F.Map.find k type_abbrevs in
      error ~loc (Format.asprintf "Type abbreviations and types must be dijoint. Type %a declared in %a" F.pp k Loc.pp lock))

  open ScopedTypeExpression

  let check_param_unique ~loc c ctx =
    if F.Set.mem c ctx then
      error ~loc ("Duplicate type parameter " ^ F.show c)

  let check_param_exists ~loc c ctx =
    if not @@ F.Set.mem c ctx then
      error ~loc (Format.asprintf "Unknown type parameter %a. Known parameters: %a" F.pp c (pplist F.pp ", ") (F.Set.elements ctx))

  let check_global_exists ~loc c (type_abbrevs : type_abbrevs) arities nargs =
    if F.Map.mem c arities then begin
      let arity, _ = F.Map.find c arities in
      if arity != nargs then
        error ~loc (Format.asprintf "Type %a expects %d arguments but was given %d" F.pp c arity nargs)
    end else if F.Map.mem c type_abbrevs then begin
      let arity = TypeAssignment.nparams @@ F.Map.find c type_abbrevs in
      if arity != nargs then
        error ~loc (Format.asprintf "Type %a expects %d arguments but was given %d" F.pp c arity nargs)
    end else
      error ~loc ("Unknown type " ^ F.show c)

  let check_type ~type_abbrevs arities ~loc ctx x =
    (* Format.eprintf "check_type under %a\n%!" (F.Map.pp (fun fmt (n,_) -> ())) arities;  *)
    (* Format.eprintf "check_type %a\n%!" ScopedTypeExpression.pp_v_ x;  *)
    let rec aux_params ~loc ctx = function
      | Lam(c,t) ->
          check_param_unique ~loc c ctx;
          TypeAssignment.Lam(c,aux_params ~loc (F.Set.add c ctx) t)
      | Ty t -> TypeAssignment.Ty(aux_loc ctx t)
    and aux_loc ctx { loc; it } = aux ~loc ctx it
    and aux ~loc ctx = function
      | Prop -> TypeAssignment.Prop
      | Any -> TypeAssignment.Any
      | Const(Local,c) ->
          check_param_exists ~loc c ctx;
          TypeAssignment.UVar c
      | Const(Global,c) ->
          check_global_exists ~loc c type_abbrevs arities 0;
          TypeAssignment.Cons c
      | App(c,x,xs) ->
          check_global_exists ~loc c type_abbrevs arities (1 + List.length xs);
          TypeAssignment.App(c,aux_loc ctx x, List.map (aux_loc ctx) xs)
      | Arrow(v,s,t) -> TypeAssignment.Arr(v,aux_loc ctx s,aux_loc ctx t)
      | Pred(_,[]) -> TypeAssignment.Prop
      | Pred(f,(_,x)::xs) -> TypeAssignment.Arr(Ast.Structured.NotVariadic,aux_loc ctx x,aux ~loc ctx (Pred(f,xs)))
    in
      aux_params ~loc ctx x

  let check_types  ~type_abbrevs arities lst =
    match List.map (fun { value; loc } -> check_type ~type_abbrevs arities ~loc F.Set.empty value) lst with
    | [] -> assert false
    | [x] -> TypeAssignment.Single x
    | xs -> TypeAssignment.Overloaded xs

  let check_type  ~type_abbrevs arities { value; loc } =
    check_type ~type_abbrevs arities ~loc F.Set.empty value

  let arrow_of_args args ety =
    let rec aux = function
    | [] -> ety
    | x :: xs -> TypeAssignment.Arr(Ast.Structured.NotVariadic,ScopedTerm.type_of x,aux xs) in
    aux args
  
  let arrow_of_tys tys ety =
    let rec aux = function
    | [] -> ety
    | x :: xs -> TypeAssignment.Arr(Ast.Structured.NotVariadic,x,aux xs) in
    aux tys
  
  type env = TypeAssignment.overloaded_skema F.Map.t

  open ScopedTerm

  let error_not_a_function ~loc c args x =
    let t =
      if args = [] then ScopedTerm.Const(Global,c)
      else ScopedTerm.(App(Global,c,List.hd args, List.tl args)) in
    let msg = Format.asprintf "@[<hov>%a is not a function but it is passed the argument@ %a@]" ScopedTerm.pretty_ t ScopedTerm.pretty x in
    error ~loc msg

  let pp_tyctx fmt = function
    | None -> Format.fprintf fmt "its context"
    | Some c -> F.pp fmt c

  let error_bad_cdata_ety ~loc ~tyctx ~ety c tx =
    let msg = Format.asprintf "@[<hov>literal %a has type %a@ but %a expects a term of type@ %a@]"  CData.pp c TypeAssignment.pretty tx pp_tyctx tyctx TypeAssignment.pretty ety in
    error ~loc msg
  
  let error_bad_ety ~loc ~tyctx ~ety pp c tx =
    let msg = Format.asprintf "@[<hov>%a has type %a@ but %a expects a term of type@ %a@]"  pp c TypeAssignment.pretty tx pp_tyctx tyctx TypeAssignment.pretty ety in
    error ~loc msg

  let error_bad_function_ety ~loc ~tyctx ~ety c t =
    let msg = Format.asprintf "@[<hov>%a is a function@ but %a expects a term of type@ %a@]"  ScopedTerm.pretty_ ScopedTerm.(Lam(c,t)) pp_tyctx tyctx TypeAssignment.pretty ety in
    error ~loc msg
  
  let error_bad_const_ety_l ~loc ~tyctx ~ety c txl =
    let msg = Format.asprintf "@[<hov>%a has type %a@ but %a expects a term of type@ %a@]"  F.pp c (pplist ~boxed:true TypeAssignment.pretty " /\\ ") txl pp_tyctx tyctx TypeAssignment.pretty ety in
    error ~loc msg

  let error_overloaded_app ~loc ~ety c args alltys =
    let ty = arrow_of_args args ety in
    let msg = Format.asprintf "@[<hov>%a is overloaded but none of its types@ matches %a.@ @[<v 2>Its types are:@ %a@]@]" F.pp c TypeAssignment.pretty ty (pplist TypeAssignment.pretty " ") alltys in
    error ~loc msg

  let error_bad_arguments ~loc c tys x tx =
    let msg = Format.asprintf "%a has type %a but %a expects an argument of one of the types: %a"
      ScopedTerm.pretty x TypeAssignment.pretty tx F.pp c
      (pplist TypeAssignment.pretty "; ") tys in
    error ~loc msg
    
  let error_not_poly ~loc ty sk =
    error ~loc (Format.asprintf "@[<hv>Type@ %a@ is less general than the declared one@ %a@]"
      TypeAssignment.pretty ty
      TypeAssignment.pretty sk)

  type ret = TypeAssignment.t MutableOnce.t TypeAssignment.t_

  let global_type env ~loc c : ret TypeAssignment.overloading =
    try TypeAssignment.fresh_overloaded @@ F.Map.find c env
    with Not_found ->
      error ~loc (Format.asprintf "Unknown global: %a" F.pp c)

  let local_type ctx ~loc c : ret TypeAssignment.overloading =
    try TypeAssignment.Single (F.Map.find c ctx)
    with Not_found -> anomaly ~loc "free variable"

  type classification =
    | Simple of { srcs : ret list; tgt : ret }
    | Variadic of { srcs : ret list; tgt : ret }
    | Unknown

  let rec classify_arrow = function
    | TypeAssignment.Arr(Ast.Structured.Variadic,x,tgt) -> Variadic { srcs = [x]; tgt }
    | UVar m when MutableOnce.is_set m -> classify_arrow (TypeAssignment.deref m)
    | UVar _ -> Unknown
    | (App _ | Prop | Cons _ | Any) as tgt -> Simple { srcs = []; tgt }
    | TypeAssignment.Arr(Ast.Structured.NotVariadic,x,xs) ->
        match classify_arrow xs with
        | Simple {srcs; tgt } -> Simple { srcs = x :: srcs; tgt }
        | Unknown -> Unknown
        | Variadic { srcs; tgt } -> Variadic { srcs = x :: srcs; tgt }

  let mk_uvar s = TypeAssignment.UVar(MutableOnce.make (F.from_string s))

  let rec extend l1 l2 =
    match l1, l2 with
    | [],_ -> assert false
    | _, [] -> []
    | [x], _:: ys -> x :: extend [x] ys
    | x::xs, _::ys -> x :: extend [x] ys

  let is_spill { it } =
    match it with
    | Spill _ -> true
    | _ -> false

  let rec any_arg_is_spill = function
    | [] -> false
    | x :: xs -> is_spill x || any_arg_is_spill xs


  let check ~type_abbrevs ~kinds ~env (t : ScopedTerm.t) ~(exp : TypeAssignment.t) =
    (* Format.eprintf "checking %a\n" ScopedTerm.pretty t; *)
    let needs_spill = ref false in
    let sigma : TypeAssignment.t F.Map.t ref = ref F.Map.empty in
    let fresh_name = let i = ref 0 in fun () -> incr i; F.from_string ("%dummy"^ string_of_int !i) in
    let rec check ctx ~loc ~tyctx x (ety : ret) : ScopedTerm.t list =
      (* Format.eprintf "checking %a\n" ScopedTerm.pretty_ x; *)
      match x with
      | Const(Global,c) -> check_global ctx ~loc ~tyctx c ety
      | Const(Local,c) -> check_local ctx ~loc ~tyctx c ety
      | CData c -> check_cdata ~loc ~tyctx kinds c ety
      | Spill(sp,n) -> assert(n=0); check_spill ctx ~loc ~tyctx sp ety
      | App(Global,c,x,xs) -> check_app ctx ~loc ~tyctx c (global_type env ~loc c) (x::xs) ety 
      | App(Local,c,x,xs) -> check_app ctx ~loc ~tyctx c (local_type ctx ~loc c) (x::xs) ety
      | Lam(c,t) -> check_lam ctx ~loc ~tyctx c t ety
      | Discard -> []
      | Var(c,args) -> check_app ctx ~loc ~tyctx c (uvar_type c) args ety

    and check_global ctx ~loc ~tyctx c ety =
      match global_type env ~loc c with
      | Single ty ->
          if unify ty ety then []
          else error_bad_ety ~tyctx ~loc ~ety F.pp c ty
      | Overloaded l ->
          if unify_first l ety then []
          else error_bad_const_ety_l ~tyctx ~loc ~ety c l

    and check_local ctx ~loc ~tyctx c ety =
      match local_type ctx ~loc c with
      | Single ty ->
          if unify ty ety then []
          else error_bad_ety ~tyctx ~loc ~ety F.pp c ty
      | Overloaded _ -> assert false

    and check_cdata ~loc ~tyctx kinds c ety =
      let name = F.from_string @@ CData.name c in
      check_global_exists ~loc name type_abbrevs kinds 0;
      let ty = TypeAssignment.Cons name in
      if unify ty ety then []
      else error_bad_cdata_ety ~tyctx ~loc c ty ~ety

    and check_lam ctx ~loc ~tyctx c t ety =
      let name = match c with Some c -> c | None -> fresh_name () in
      let src = mk_uvar "Src" in
      let tgt = mk_uvar "Tgt" in
      if unify (TypeAssignment.Arr(Ast.Structured.NotVariadic,src,tgt)) ety then
        check_loc ~tyctx (F.Map.add name src ctx) t ~ety:tgt
      else
        error_bad_function_ety ~loc ~tyctx ~ety c t

    and check_spill ctx ~loc ~tyctx sp ety =
      needs_spill := true;
      let inner_spills = check_loc ~tyctx:None ctx sp ~ety:(mk_uvar "Spill") in (* TODO?? *)
      let phantom_of_spill_ty i ty =
        { loc; it = Spill(sp,i+1); ty = MutableOnce.create (TypeAssignment.Val ty) } in
      match classify_arrow (ScopedTerm.type_of sp) with
      | Simple { srcs; tgt } ->
          if not @@ unify tgt Prop then error ~loc "only predicated can be spilled";
          let spills = srcs in
          let first_spill = List.hd spills in
          if unify first_spill ety then List.mapi phantom_of_spill_ty @@ List.tl spills
          else error_bad_ety ~tyctx ~loc ~ety ScopedTerm.pretty_ (Spill(sp,0)) first_spill
      | _ -> error ~loc "hard spill"

    and check_app ctx ~loc ~tyctx c cty args ety =
      match cty with
      | Overloaded l ->
        let args = List.concat_map (fun x -> x :: check_loc ~tyctx:None ctx ~ety:(mk_uvar "Ety") x) args in
        let targs = List.map ScopedTerm.type_of args in
        check_app_overloaded ctx ~loc c ety args targs l l
      | Single ty ->
          let err () =
            if args = [] then error_bad_ety ~loc ~tyctx ~ety F.pp c ty (* uvar *)
            else error_bad_ety ~loc ~tyctx ~ety ScopedTerm.pretty_ (App(Global (* sucks *),c,List.hd args,List.tl args)) ty in
          let monodirectional () =
            (* Format.eprintf "checking app mono %a\n" F.pp c; *)
            let tgt = check_app_single ctx ~loc c ty [] args in
            if unify tgt ety then []
            else err () in
          let bidirectional srcs tgt =
            (* Format.eprintf "checking app bidi %a\n" F.pp c; *)
            let rec consume args srcs =
              match args, srcs with
              | [], srcs -> arrow_of_tys srcs tgt
              | _ :: args, _ :: srcs -> consume args srcs
              | _ :: _, [] -> assert false
            in
            let rest_tgt = consume args srcs in
            if unify rest_tgt ety then
              let _ = check_app_single ctx ~loc c ty [] args in []
            else err () in
          match classify_arrow ty with
          | Unknown | Variadic _ -> monodirectional ()
          | Simple { srcs; tgt } ->
            if List.length args > List.length srcs then monodirectional () (* will error *)
            else
              if any_arg_is_spill args then monodirectional ()
              else bidirectional srcs tgt

            (* XXX ... look at args, is no spill then build arrow using srcs -> tgt - args .. *)

    and check_app_overloaded ctx ~loc c ety args targs alltys = function
      | [] -> error_overloaded_app ~loc c args ~ety alltys
      | t::ts ->
          (* Format.eprintf "checking overloaded app %a\n" F.pp c; *)
          match classify_arrow t with
          | Unknown -> error ~loc "Type too ambiguous to be assigned to an overloaded constant"
          | Simple { srcs; tgt } ->
              if try_unify_all (tgt::srcs) (ety::targs) then []
              else check_app_overloaded ctx ~loc c ety args targs alltys ts
          | Variadic { srcs ; tgt } ->
              let srcs = extend srcs targs in
              if try_unify_all (tgt::srcs) (ety::targs) then []
              else check_app_overloaded ctx ~loc c ety args targs alltys ts

    and check_app_single ctx ~loc c ty consumed args =
      match args with
      | [] -> ty
      | x :: xs ->
        (* Format.eprintf "checking app %a @ %a\n" F.pp c ScopedTerm.pretty x; *)
        match ty with
          | TypeAssignment.Arr(Ast.Structured.Variadic,s,t) ->
              let xs = check_loc_if_not_phantom ~tyctx:(Some c) ctx x ~ety:s @ xs in
              if xs = [] then t else check_app_single ctx ~loc c ty (x::consumed) xs
          | TypeAssignment.Arr(Ast.Structured.NotVariadic,s,t) ->
              let xs = check_loc_if_not_phantom ~tyctx:(Some c) ctx x ~ety:s @ xs in
              check_app_single ctx ~loc c t (x::consumed)  xs
          | TypeAssignment.UVar m when MutableOnce.is_set m ->
              check_app_single ctx ~loc c (TypeAssignment.deref m) consumed (x :: xs)
          | TypeAssignment.UVar m ->
              let s = mk_uvar "Src" in
              let t = mk_uvar "Tgt" in
              check_app_single ctx ~loc c (TypeAssignment.Arr(Ast.Structured.NotVariadic,s,t)) consumed (x :: xs)
          | _ -> error_not_a_function ~loc:x.loc c (List.rev consumed) x (* TODO: trim loc up to x *)

    and check_loc ~tyctx ctx { loc; it; ty } ~ety : ScopedTerm.t list =
      assert (not @@ MutableOnce.is_set ty);
      let extra_spill = check ~tyctx ctx ~loc it ety in
      MutableOnce.set ty (Val ety);
      extra_spill

    and check_loc_if_not_phantom ~tyctx ctx x ~ety : ScopedTerm.t list =
      match x.it with
      | Spill(_,n) when n > 0 -> []
      | _ -> check_loc ~tyctx ctx x ~ety

    and check_matches_poly_skema_loc { loc; it } =
      let c, args =
        match it with
        | App(Global,c, { it = App(Global,c',x,xs) },_) when F.equal F.rimplf c -> c', x :: xs
        | App(Global,c, { it = Const(Global,c') },_) when F.equal F.rimplf c -> c', []
        | App(Global,c,x,xs) -> c, x :: xs
        | Const(Global,c) -> c, []
        | _ -> assert false in
      (* Format.eprintf "Checking %a\n" F.pp c; *)
      match F.Map.find c env with
      | Single (Ty _) -> ()
      | Single (Lam _ as sk) -> check_matches_poly_skema ~loc ~pat:(TypeAssignment.fresh sk) (arrow_of_args args TypeAssignment.Prop)
      | Overloaded _ -> ()

    and check_matches_poly_skema ~loc ~pat ty =
      if try_matching ~pat ty then () else error_not_poly ~loc ty (fst pat)

    and try_unify_all xl yl =
      let vx = List.fold_left (fun xs t -> TypeAssignment.vars_of (Val t) @ xs) [] xl in
      let vy = List.fold_left (fun xs t -> TypeAssignment.vars_of (Val t) @ xs) [] yl in
      let b = Util.for_all2 unify xl yl in
      if not b then (undo vx; undo vy);
      b
    
    and unify_first l ety =
      let vars = TypeAssignment.vars_of (Val ety) in
      let rec aux = function
        | [] -> false
        | x::xs -> if unify x ety then true else (undo vars; aux xs)
      in
        aux l
  
    and undo = function
      | [] -> ()
      | m :: ms -> MutableOnce.unset m; undo ms

    and uvar_type c =
      try TypeAssignment.Single (TypeAssignment.unval @@ F.Map.find c !sigma)
      with Not_found ->
        let ty = TypeAssignment.UVar (MutableOnce.make c) in
        sigma := F.Map.add c (TypeAssignment.Val ty) !sigma;
        TypeAssignment.Single ty
    and unif ~matching t1 t2 =
      (* Format.eprintf "%a = %a\n" TypeAssignment.pretty t1 TypeAssignment.pretty t2; *)
      let open TypeAssignment in
      match t1, t2 with
      | Any, _ -> true
      | _, Any -> true
      | UVar m, _ when MutableOnce.is_set m -> unif ~matching (TypeAssignment.deref m) t2
      | _, UVar m when MutableOnce.is_set m -> unif ~matching t1 (TypeAssignment.deref m)
      | App(c1,x,xs), App(c2,y,ys) when F.equal c1 c2 ->
         unif ~matching x y && Util.for_all2 (unif ~matching) xs ys
      | Cons c1, Cons c2 when F.equal c1 c2 -> true
      | Prop, Prop -> true
      | Arr(b1,s1,t1), Arr(b2,s2,t2) -> b1 == b2 && unif ~matching s1 s2 && unif ~matching t1 t2      
      | Arr(Ast.Structured.Variadic,_,t), _ -> unif ~matching t t2
      | _, Arr(Ast.Structured.Variadic,_,t) -> unif ~matching t1 t
      | UVar m, UVar n when matching -> assign m t2
      | UVar m, _ when not matching -> assign m t2
      | _, UVar m -> assign m t1
      | Cons c, _ when F.Map.mem c type_abbrevs ->
          let t1 = apply (F.Map.find c type_abbrevs) [] in
          unif ~matching t1 t2
      | _, Cons c when F.Map.mem c type_abbrevs ->
          let t2 = apply (F.Map.find c type_abbrevs) [] in
          unif ~matching t1 t2
      | App(c,x,xs), _ when F.Map.mem c type_abbrevs ->
          let t1 = apply (F.Map.find c type_abbrevs) (x::xs) in
          unif ~matching t1 t2
      | _, App(c,x,xs) when F.Map.mem c type_abbrevs ->
          let t2 = apply (F.Map.find c type_abbrevs) (x::xs) in
          unif ~matching t1 t2
      | _,_ -> false

    and unify x y = unif ~matching:false x y
    and try_matching ~pat:(x,vars) y =
      let vars = F.Map.bindings vars |> List.map snd |> List.map cell_of in
      let deref x = cell_of (TypeAssignment.deref x) in
      if unif ~matching:true x y then
        if disjoint (List.map deref vars) then true
        else (undo vars; false)
      else
        (undo vars; false)

    and cell_of = function
      | TypeAssignment.UVar x -> x
      | _ -> assert false

    and disjoint = function
        | [] -> true
        | x :: xs -> not (List.exists (fun y -> same_var y (TypeAssignment.UVar x)) xs) && disjoint xs

    and assign m t = same_var m t || (oc m t && ((*Format.eprintf "%a := %a\n" MutableOnce.(pp TypeAssignment.pp) m TypeAssignment.(pp_t_ MutableOnce.(pp TypeAssignment.pp)) t;*)TypeAssignment.set m t; true))

    and same_var m = function
      | UVar n when n == m -> true
      | UVar n when MutableOnce.is_set n -> same_var m (TypeAssignment.deref n)
      | _ -> false

    and oc m = function
      | Prop -> true
      | Arr(_,x,y) -> oc m x && oc m y
      | App(_,x,xs) -> List.for_all (oc m) (x::xs)
      | Any -> true
      | Cons _ -> true
      | UVar n when m == n -> false
      | UVar n when MutableOnce.is_set n -> oc m (TypeAssignment.deref n)
      | UVar _ -> true

    in
      let spills = check_loc ~tyctx:None F.Map.empty t ~ety:(TypeAssignment.unval exp) in
      check_matches_poly_skema_loc t;
      if spills <> [] then error ~loc:t.loc "cannot spill in head";
      !needs_spill

  (* let check ~type_abbrevs a b c =
    try check ~type_abbrevs a b c with
    | CompileError(_,"Unknown global: %spill") -> Printf.eprintf "SPILLING"; exit 1
    | CompileError(_,s) when Re.Str.(string_match (regexp "Unknown global: @")) s 0 -> Printf.eprintf "MACRO"; exit 1
    | CompileError(loc,msg) -> Format.eprintf "Ignoring type error: %a %s\n" (Util.pp_option Loc.pp) loc msg; TypeAssignment.(Val Prop) *)
end



  
type macro_declaration = (ScopedTerm.t * Loc.t) F.Map.t
[@@ deriving show, ord]

module Scoped = struct


type program = {
  pbody : pbody;
  toplevel_macros : macro_declaration;
}
and pbody = {
  kinds : Arity.t F.Map.t;
  types : TypeList.t F.Map.t;
  type_abbrevs : (F.t * ScopedTypeExpression.t) list;
  modes : (mode * Loc.t) F.Map.t;
  body : block list;
  symbols : F.Set.t;
}
and block =
  | Clauses of (ScopedTerm.t,Ast.Structured.attribute) Ast.Clause.t list (* TODO: use a map : predicate -> clause list to speed up insertion *)
  | Namespace of string * pbody
  | Shorten of F.t Ast.Structured.shorthand list * pbody
  | Constraints of (F.t,ScopedTerm.t) Ast.Structured.block_constraint * pbody
  | Accumulated of pbody
[@@deriving show, ord]

end



module Flat = struct


type program = {
  toplevel_macros : macro_declaration;
  kinds : Arity.t F.Map.t;
  types : TypeList.t F.Map.t;
  type_abbrevs : (F.t * ScopedTypeExpression.t) list;
  modes : (mode * Loc.t) F.Map.t;
  clauses : (ScopedTerm.t,Ast.Structured.attribute) Ast.Clause.t list;
  chr : (F.t,ScopedTerm.t) Ast.Structured.block_constraint list;
  builtins : BuiltInPredicate.t list;
}
[@@deriving show, ord]

end

type compilation_unit = {
  version : string;
  code : Flat.program;
}
[@@deriving show]

module Assembled = struct

type program = {
  (* clauses : (ScopedTerm.t,Ast.Structured.attribute) Ast.Clause.t list; for printing *)
  kinds : Arity.t F.Map.t;
  types : TypeAssignment.overloaded_skema F.Map.t;
  type_abbrevs : TypeAssignment.skema F.Map.t;
  modes : (mode * Loc.t) F.Map.t;
  total_type_checking_time : float;

  prolog_program : index;
  indexing : (mode * indexing) C.Map.t;
  chr : CHR.t;

  symbols : SymbolMap.table;

  toplevel_macros : macro_declaration;
}
and attribute = {
  id : string option;
  timestamp : grafting_time;
  insertion : Ast.Structured.insertion option;
}
[@@deriving show]

let empty () = {
  kinds = F.Map.empty;
  types = F.Map.add F.mainf TypeAssignment.(Single (Ty Prop)) F.Map.empty;
  type_abbrevs = F.Map.empty; modes = F.Map.empty;
  prolog_program = { idx = Ptmap.empty; time = 0; times = StrMap.empty };
  indexing = C.Map.empty;
  chr = CHR.empty;
  symbols = SymbolMap.empty ();
  toplevel_macros = F.Map.empty;
  total_type_checking_time = 0.0;
}

end


type builtins = string * Data.BuiltInPredicate.declaration list

type header = State.t * compilation_unit * macro_declaration
type program = State.t * Assembled.program


module WithMain = struct

(* The entire program + query, but still in "printable" format *)
type 'a query = {
  kinds : Arity.t F.Map.t;
  types : TypeAssignment.overloaded_skema F.Map.t;
  type_abbrevs : TypeAssignment.skema F.Map.t;
  modes : (mode * Loc.t) F.Map.t;
  (* clauses : (preterm,Assembled.attribute) Ast.Clause.t list; *)
  prolog_program : index;
  chr : CHR.t;
  symbols : SymbolMap.table;
  (* query : ScopedTerm.t; *)
  query_arguments : 'a Query.arguments [@opaque];
  (* We pre-compile the query to ease the API *)
  initial_goal : term;
  assignments : term StrMap.t;
  compiler_state : State.t;
  total_type_checking_time : float;
}
[@@deriving show]

end
type 'a query = 'a WithMain.query

(****************************************************************************
  Compiler
 ****************************************************************************)

module RecoverStructure : sig

  (* Reconstructs the structure of the AST (i.e. matches { with }) *)

  val run : State.t -> Ast.Program.t -> Ast.Structured.program

end = struct (* {{{ *)

  open Ast.Structured
  open Ast

  let cl2b = function
    | [] -> []
    | clauses -> [Clauses (List.rev clauses)]

  let structure_clause_attributes ({ Clause.attributes; loc } as c) =
    let duplicate_err s =
      error ~loc ("duplicate attribute " ^ s) in
    let illegal_err a =
      error ~loc ("illegal attribute " ^ show_raw_attribute a) in
    let illegal_replace s =
      error ~loc ("replacing clause for "^ s ^" cannot have a name attribute") in
    let illegal_remove_id s =
      error ~loc ("remove clause for "^ s ^" cannot have a name attribute") in
    let rec aux_attrs r = function
      | [] -> r
      | Name s :: rest ->
         if r.id <> None then duplicate_err "name";
         aux_attrs { r with id = Some s } rest
      | After s :: rest ->
         if r.insertion <> None then duplicate_err "insertion";
         aux_attrs { r with insertion = Some (Insert (After s)) } rest
      | Before s :: rest ->
         if r.insertion <> None then duplicate_err "insertion";
         aux_attrs { r with insertion = Some (Insert (Before s)) } rest
      | Replace s :: rest ->
          if r.insertion <> None then duplicate_err "insertion";
          aux_attrs { r with insertion = Some (Replace s) } rest
      | Remove s :: rest ->
          if r.insertion <> None then duplicate_err "insertion";
          aux_attrs { r with insertion = Some (Remove s) } rest
      | If s :: rest ->
         if r.ifexpr <> None then duplicate_err "if";
         aux_attrs { r with ifexpr = Some s } rest
      | Untyped :: rest -> aux_attrs { r with typecheck = false } rest
      | (External | Index _ | Functional) as a :: _-> illegal_err a
    in
    let attributes = aux_attrs { insertion = None; id = None; ifexpr = None; typecheck = true } attributes in
    begin
      match attributes.insertion, attributes.id with
      | Some (Replace x), Some _ -> illegal_replace x
      | Some (Remove x), Some _ -> illegal_remove_id x
      | _ -> ()
    end;
    { c with Clause.attributes }

  let structure_chr_attributes ({ Chr.attributes; loc } as c) =
    let duplicate_err s =
      error ~loc ("duplicate attribute " ^ s) in
    let illegal_err a =
      error ~loc ("illegal attribute " ^ show_raw_attribute a) in
    let rec aux_chr r = function
      | [] -> r
      | Name s :: rest ->
         aux_chr { r with cid = s } rest
      | If s :: rest ->
         if r.cifexpr <> None then duplicate_err "if";
         aux_chr { r with cifexpr = Some s } rest
      | (Before _ | After _ | Replace _ | Remove _ | External | Index _ | Functional | Untyped) as a :: _ -> illegal_err a 
    in
    let cid = Loc.show loc in
    { c with Chr.attributes = aux_chr { cid; cifexpr = None } attributes }


  let rec structure_type_expression_aux ~loc valid t = { t with TypeExpression.tit =
    match t.TypeExpression.tit with
    | TypeExpression.TPred(att,p) when valid att <> None -> TypeExpression.TPred(Option.get (valid att),List.map (fun (m,p) -> m, structure_type_expression_aux ~loc valid p) p)
    | TypeExpression.TPred([], _) -> assert false
    | TypeExpression.TPred(a :: _, _) -> error ~loc ("illegal attribute " ^ show_raw_attribute a)
    | TypeExpression.TArr(s,t) -> TypeExpression.TArr(structure_type_expression_aux ~loc valid s,structure_type_expression_aux ~loc valid t) 
    | TypeExpression.TApp(c,x,xs) -> TypeExpression.TApp(c,structure_type_expression_aux ~loc valid x,List.map (structure_type_expression_aux ~loc valid) xs)
    | TypeExpression.TConst c -> TypeExpression.TConst c
  }

  let structure_type_expression loc toplevel_func valid t = 
    match t.TypeExpression.tit with
    | TypeExpression.TPred([],p) ->
      { t with TypeExpression.tit = TypeExpression.TPred(toplevel_func,List.map (fun (m,p) -> m, structure_type_expression_aux ~loc valid p) p) }
    | x -> structure_type_expression_aux ~loc valid t

  let structure_kind_attributes { Type.attributes; loc; name; ty } =
    let ty = structure_type_expression loc () (function [] -> Some () | _ -> None) ty in
    match attributes with
    | [] -> { Type.attributes = (); loc; name; ty }
    | x :: _ -> error ~loc ("illegal attribute " ^ show_raw_attribute x)

  let valid_functional = function [] -> Some Relation | [Functional] -> Some Function | _ -> None

  let structure_type_attributes { Type.attributes; loc; name; ty } =
    let duplicate_err s =
      error ~loc ("duplicate attribute " ^ s) in
    let illegal_err a =
      error ~loc ("illegal attribute " ^ show_raw_attribute a) in
    let rec aux_tatt r f = function
      | [] -> r, f
      | External :: rest ->
         begin match r with
           | None -> aux_tatt (Some Structured.External) f rest
           | Some Structured.External -> duplicate_err "external"
           | Some _ -> error ~loc "external predicates cannot be indexed"
         end
      | Index(i,index_type) :: rest ->
         let it =
           match index_type with
           | None -> None
           | Some "Map" -> Some Map
           | Some "Hash" -> Some HashMap
           | Some "DTree" -> Some DiscriminationTree
           | Some s -> error ~loc ("unknown indexing directive " ^ s ^ ". Valid ones are: Map, Hash, DTree.") in
         begin match r with
           | None -> aux_tatt (Some (Structured.Index(i,it))) f rest
           | Some (Structured.Index _) -> duplicate_err "index"
           | Some _ -> error ~loc "external predicates cannot be indexed"
         end
      | Functional :: rest -> aux_tatt r Structured.Function rest
      | (Before _ | After _ | Replace _ | Remove _ | Name _ | If _ | Untyped) as a :: _ -> illegal_err a 
    in
    let attributes, toplevel_func = aux_tatt None Structured.Relation attributes in
    let attributes =
      match attributes with
      | None -> Structured.Index([1],None)
      | Some x -> x in
    let ty = structure_type_expression loc toplevel_func valid_functional ty in
    { Type.attributes; loc; name; ty }

  let structure_type_abbreviation { TypeAbbreviation.name; value; nparams; loc } =
    let rec aux = function
      | TypeAbbreviation.Lam(c,loc,t) -> TypeAbbreviation.Lam(c,loc,aux t)
      | TypeAbbreviation.Ty t -> TypeAbbreviation.Ty (structure_type_expression loc Relation valid_functional t)
  in
  { TypeAbbreviation.name; value = aux value; nparams; loc }

  let run _ dl =
    let rec aux_run ns blocks clauses macros kinds types tabbrs modes chr accs = function
      | Program.Ignored _ :: rest ->
          aux_run ns blocks clauses macros kinds types tabbrs modes chr accs rest
      | (Program.End _ :: _ | []) as rest ->
          { body = List.rev (cl2b clauses @ blocks);
            types = List.rev types;
            kinds = List.rev kinds;
            type_abbrevs = List.rev tabbrs;
            macros = List.rev macros;
            modes = List.rev modes },
          List.rev chr,
          rest
      | Program.Begin loc :: rest ->
          let p, chr1, rest = aux_run ns [] [] [] [] [] [] [] [] accs rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside an anonymous block";
          aux_end_block loc ns (Accumulated p :: cl2b clauses @ blocks)
            [] macros kinds types tabbrs modes chr accs rest
      | Program.Constraint (loc, ctx_filter, clique) :: rest ->
          if chr <> [] then
            error "Constraint blocks cannot be nested";
          let p, chr, rest = aux_run ns [] [] [] [] [] [] [] [] accs rest in
          aux_end_block loc ns (Constraints({ctx_filter;clique;rules=chr},p) :: cl2b clauses @ blocks)
            [] macros kinds types tabbrs modes [] accs rest
      | Program.Namespace (loc, n) :: rest ->
          let p, chr1, rest = aux_run (n::ns) [] [] [] [] [] [] [] [] StrSet.empty rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside a namespace block";
          aux_end_block loc ns (Namespace (n,p) :: cl2b clauses @ blocks)
            [] macros kinds types tabbrs modes chr accs rest
      | Program.Shorten (loc,[]) :: _ ->
          anomaly ~loc "parser returns empty list of shorten directives"
      | Program.Shorten (loc,directives) :: rest ->
          let shorthand (full_name,short_name) = { iloc = loc; full_name; short_name } in
          let shorthands = List.map shorthand directives in
          let p, chr1, rest = aux_run ns [] [] [] [] [] [] [] [] accs rest in
          if chr1 <> [] then
            error "CHR cannot be declared after a shorthand";
          aux_run ns ((Shorten(shorthands,p) :: cl2b clauses @ blocks))
            [] macros kinds types tabbrs modes chr accs rest

      | Program.Accumulated (_,[]) :: rest ->
          aux_run ns blocks clauses macros kinds types tabbrs modes chr accs rest

      | Program.Accumulated (loc,(filename,digest,a) :: more) :: rest ->
          let rest = Program.Accumulated (loc, more) :: rest in
          let digest = String.concat "." (digest :: List.map F.show ns) in
          if StrSet.mem digest accs then begin
            (* Printf.eprintf "skip: %s\n%!" filename; *)
            aux_run ns blocks clauses macros kinds types tabbrs modes chr accs rest
          end else begin
            (* Printf.eprintf "acc: %s -> %d\n%!" filename (List.length a); *)
            aux_run ns blocks clauses macros kinds types tabbrs modes chr
              (StrSet.add digest accs)
              (Program.Begin loc :: a @ Program.End loc :: rest)
          end

      | Program.Clause c :: rest ->
          let c = structure_clause_attributes c in
          aux_run ns blocks (c::clauses) macros kinds types tabbrs modes chr accs rest
      | Program.Macro m :: rest ->
          aux_run ns blocks clauses (m::macros) kinds types tabbrs modes chr accs rest
      | Program.Pred t :: rest ->
          let t = structure_type_attributes t in
          aux_run ns blocks clauses macros kinds (t :: types) tabbrs (t::modes) chr accs rest
      | Program.Kind [] :: rest ->
          aux_run ns blocks clauses macros kinds types tabbrs modes chr accs rest
      | Program.Kind (k::ks) :: rest ->          
          let k = structure_kind_attributes k in
          aux_run ns blocks clauses macros (k :: kinds) types tabbrs modes chr accs (Program.Kind ks :: rest)
      | Program.Type [] :: rest ->
          aux_run ns blocks clauses macros kinds types tabbrs modes chr accs rest
      | Program.Type (t::ts) :: rest ->          
          if List.mem Functional t.attributes then error ~loc:t.loc "functional attribute only applies to pred";
          let t = structure_type_attributes t in
          aux_run ns blocks clauses macros kinds (t :: types) tabbrs modes chr accs (Program.Type ts :: rest)
      | Program.TypeAbbreviation abbr :: rest ->
          let abbr = structure_type_abbreviation abbr in
          aux_run ns blocks clauses macros kinds types (abbr :: tabbrs) modes chr accs rest
      | Program.Chr r :: rest ->
          let r = structure_chr_attributes r in
          aux_run ns blocks clauses macros kinds types tabbrs modes (r::chr) accs rest

    and aux_end_block loc ns blocks clauses macros kinds types tabbrs modes chr accs rest =
      match rest with
      | Program.End _ :: rest ->
          aux_run ns blocks clauses macros kinds types tabbrs modes chr accs rest
      | _ -> error ~loc "matching } is missing"

    in
    let blocks, chr, rest = aux_run [] [] [] [] [] [] [] [] [] StrSet.empty dl in
    begin match rest with
    | [] -> ()
    | Program.End loc :: _ -> error ~loc "extra }"
    | _ -> assert false
    end;
    if chr <> [] then
      error "CHR cannot be declared outside a Constraint block";
    blocks

end (* }}} *)


module Quotation = struct

  let named_quotations : QuotationHooks.quotation StrMap.t State.component = State.declare
    ~descriptor:elpi_state_descriptor
    ~name:"elpi:named_quotations"
    ~pp:(fun _ _ -> ())
    ~clause_compilation_is_over:(fun b -> b)
    ~goal_compilation_begins:(fun b -> b)
    ~goal_compilation_is_over:(fun ~args:_ b -> Some b)
    ~compilation_is_over:(fun x -> Some x)
    ~execution_is_over:(fun x -> Some x)
    ~init:(fun () -> StrMap.empty)
  let default_quotation : QuotationHooks.quotation option State.component = State.declare
    ~descriptor:elpi_state_descriptor
    ~name:"elpi:default_quotation"
    ~pp:(fun _ _ -> ())
    ~clause_compilation_is_over:(fun b -> b)
    ~goal_compilation_begins:(fun b -> b)
    ~goal_compilation_is_over:(fun ~args:_ b -> Some b)
    ~compilation_is_over:(fun x -> Some x)
    ~execution_is_over:(fun x -> Some x)
    ~init:(fun () -> None)

end

include Quotation

module CustomFunctorCompilation = struct

  let is_singlequote x =
    let s = F.show x in
    let len = String.length s in
    len > 2 && s.[0] == '\'' && s.[len-1] == '\''

  let is_backtick x =
    let s = F.show x in
    let len = String.length s in
    len > 2 && s.[0] == '`' && s.[len-1] == '`'

  let singlequote : (State.t -> F.t -> State.t * term) option State.component = State.declare
  ~descriptor:elpi_state_descriptor
  ~name:"elpi:singlequote"
  ~pp:(fun _ _ -> ())
  ~clause_compilation_is_over:(fun b -> b)
  ~goal_compilation_begins:(fun b -> b)
  ~goal_compilation_is_over:(fun ~args:_ b -> Some b)
  ~compilation_is_over:(fun x -> Some x)
  ~execution_is_over:(fun x -> Some x)
  ~init:(fun () -> None)

  let backtick  : (State.t -> F.t -> State.t * term) option State.component = State.declare
  ~descriptor:elpi_state_descriptor
  ~name:"elpi:backtick"
  ~pp:(fun _ _ -> ())
  ~clause_compilation_is_over:(fun b -> b)
  ~goal_compilation_begins:(fun b -> b)
  ~goal_compilation_is_over:(fun ~args:_ b -> Some b)
  ~compilation_is_over:(fun x -> Some x)
  ~execution_is_over:(fun x -> Some x)
  ~init:(fun () -> None)

  let compile_singlequote state x = assert false
  (* 
    match State.get singlequote state with
    | None -> let state, (_,t) = Symbols.allocate_global_symbol state x in state, t
    | Some f -> f state x *)
  let compile_backtick state x = assert false (*
    match State.get backtick state with
    | None -> let state, (_,t) = Symbols.allocate_global_symbol state x in state, t
    | Some f -> f state x
 *)
end

let namespace_separatorc = '.'
let namespace_separator = String.make 1 namespace_separatorc

let prefix_const prefix c =
  F.from_string (String.concat namespace_separator (prefix @ [F.show c]))

let prepend p s =
  F.Set.map (prefix_const p) s

let has_dot f =
  try let _ = String.index (F.show f) namespace_separatorc in true
  with Not_found -> false


module Scope_Quotation_Macro : sig

  val run : State.t -> Ast.Structured.program -> State.t * Scoped.program
  val check_duplicate_mode : F.t -> (mode * Loc.t) -> (mode * Loc.t) F.Map.t -> unit
  val scope_loc_term : Ast.Term.t -> ScopedTerm.t

end = struct
  let map_append k v m =
    try
      let l = F.Map.find k m in
      F.Map.add k (TypeList.merge v l) m
    with Not_found ->
      F.Map.add k v m

  let is_uvar_name f =  F.is_uvar_name f

  let is_discard f =
    F.(equal f dummyname) ||
    let c = (F.show f).[0] in
      c = '_'

  let is_macro_name f =
      let c = (F.show f).[0] in
      c = '@'

  let rec scope_term ctx ~loc t =
    let open Ast.Term in
    match t with
    | Const c when is_discard c -> ScopedTerm.Discard
    | Const c when F.Set.mem c ctx -> ScopedTerm.(Const(Local,c))
    | Const c ->
        if is_uvar_name c then ScopedTerm.Var(c,[])
        else ScopedTerm.(Const(Global,c))
    | App ({ it = App (f,l1) },l2) -> scope_term ctx ~loc (App(f, l1 @ l2))
    | App({ it = Const c }, [x]) when F.equal c F.spillf ->
        ScopedTerm.Spill (scope_loc_term ctx x,0)
    | App({ it = Const c }, x :: xs) ->
         if is_discard c then error ~loc "Applied discard";
         let x = scope_loc_term ctx x in
         let xs = List.map (scope_loc_term ctx) xs in
         let bound = F.Set.mem c ctx in
         if bound then ScopedTerm.App(Local, c, x, xs)
         else if is_uvar_name c then ScopedTerm.Var(c,x :: xs)
         else ScopedTerm.App(Global, c, x, xs)
    | Lam (c,b) when is_discard c -> ScopedTerm.Lam (None,scope_loc_term ctx b)
    | Lam (c,b) ->
        if has_dot c then error ~loc "Bound variables cannot contain the namespaec separator '.'";
        ScopedTerm.Lam (Some c,scope_loc_term (F.Set.add c ctx) b)
    | CData c -> ScopedTerm.CData c (* CData.hcons *)
    | Quoted _ -> assert false (* TODO *)
    | App ({ it = Const _},[]) -> anomaly "Application node with no arguments"
    | App ({ it = Lam _},_) ->
      error ~loc "Beta-redexes not allowed, use something like (F = x\\x, F a)"
    | App ({ it = CData _},_) ->
      error ~loc "Applied literal"
    | App ({ it = Quoted _},_) ->
      error ~loc "Applied quotation"
  and scope_loc_term ctx { Ast.Term.it; loc } =
    let it = scope_term ctx ~loc it in
    { ScopedTerm.it; loc; ty = MutableOnce.make (F.from_string "Ty") }

  let scope_loc_term = scope_loc_term F.Set.empty

  let rec scope_tye ctx ~loc t =
    match t with
    | Ast.TypeExpression.TConst c when F.show c = "prop" -> ScopedTypeExpression.Prop
    | Ast.TypeExpression.TConst c when F.show c = "any" -> ScopedTypeExpression.Any
    | Ast.TypeExpression.TConst c when F.Set.mem c ctx -> ScopedTypeExpression.(Const(ScopeContext.Local,c))
    | Ast.TypeExpression.TConst c -> ScopedTypeExpression.(Const(ScopeContext.Global,c))
    | Ast.TypeExpression.TApp(c,x,[y]) when F.show c = "variadic" ->
        ScopedTypeExpression.Arrow(Ast.Structured.Variadic,scope_loc_tye ctx x,scope_loc_tye ctx y)
    | Ast.TypeExpression.TApp(c,x,xs) ->
        if F.Set.mem c ctx || is_uvar_name c then error ~loc "type schema parameters cannot be type formers";
        ScopedTypeExpression.App(c,scope_loc_tye ctx x, List.map (scope_loc_tye ctx) xs)
    | Ast.TypeExpression.TPred(m,xs) ->
        ScopedTypeExpression.Pred(m,List.map (fun (m,t) -> m, scope_loc_tye ctx t) xs)
    | Ast.TypeExpression.TArr(s,t) ->
        ScopedTypeExpression.Arrow(Ast.Structured.NotVariadic, scope_loc_tye ctx s, scope_loc_tye ctx t)
  and scope_loc_tye ctx { tloc; tit } = { loc = tloc; it = scope_tye ctx ~loc:tloc tit }

  let scope_type_abbrev { Ast.TypeAbbreviation.name; value; nparams; loc } =
    let rec aux ctx = function
      | Ast.TypeAbbreviation.Lam(c,loc,t) when is_uvar_name c ->
          if F.Set.mem c ctx then error ~loc "duplicate type schema variable";
          ScopedTypeExpression.Lam(c,aux (F.Set.add c ctx) t)
      | Ast.TypeAbbreviation.Lam(c,loc,_) -> error ~loc "only variables can be abstracted in type schema"
      | Ast.TypeAbbreviation.Ty t -> ScopedTypeExpression.Ty (scope_loc_tye ctx t)
  in
    { ScopedTypeExpression.name; value = aux F.Set.empty value; nparams; loc; indexing = None }

  let compile_type { Ast.Type.name; loc; attributes; ty } =
    let open ScopedTypeExpression in
    let value = scope_loc_tye F.Set.empty ty in
    let vars =
      let rec aux e { it } =
        match it with
        | App(_,x,xs) -> List.fold_left aux e (x :: xs)
        | Const(Local, _) -> assert false (* there are no binders yet *)
        | Const(Global,c) when is_uvar_name c -> F.Set.add c e
        | Const(Global,_) -> e
        | Prop -> e
        | Any -> e
        | Arrow(_,x,y) -> aux (aux e x) y
        | Pred(_,l) -> List.fold_left aux e (List.map snd l)
      in
        aux F.Set.empty value in
    let value = scope_loc_tye vars ty in
    let nparams = F.Set.cardinal vars in
    let value =
      let rec close s t =
        if F.Set.is_empty s then t
        else
          let c = F.Set.choose s in
          let s = F.Set.remove c s in
          close s (Lam(c,t)) in
      close vars (Ty value) in
    { ScopedTypeExpression.name; indexing = Some attributes; loc; nparams; value }

  let compile_type_abbrev ({ Ast.TypeAbbreviation.name; nparams; loc } as ab) =
    let ab = scope_type_abbrev ab in
    name, ab

  let check_duplicate_mode name (mode, loc) map =
    if F.Map.mem name map && fst (F.Map.find name map) <> mode then
      error ~loc
        ("Duplicate mode declaration for " ^ F.show name ^ " (also at "^
          Loc.show (snd (F.Map.find name map)) ^ ")")

  let compile_mode modes { Ast.Type.name; loc; ty = { Ast.TypeExpression.tit } } =
    let fix_mode = function Ast.Mode.Input -> Util.Input | Ast.Mode.Output -> Util.Output in 
    let rec type_to_mode = function
      | m, Ast.TypeExpression.{ tit = TPred(_,l) } -> Ho(fix_mode m,List.map type_to_mode l)
      | m, _ -> Fo (fix_mode m) in
    match tit with
    | Ast.TypeExpression.TPred(_,l) ->
        let args = List.map type_to_mode l in
       check_duplicate_mode name (args,loc) modes;
       F.Map.add name (args,loc) modes
    | _ -> modes

  let defs_of_map m = F.Map.bindings m |> List.fold_left (fun x (a,_) -> F.Set.add a x) F.Set.empty
  let defs_of_assoclist m = m |> List.fold_left (fun x (a,_) -> F.Set.add a x) F.Set.empty

  let global_hd_symbols_of_clauses cl =
    let open ScopedTerm in
    List.fold_left (fun s { Ast.Clause.body = { it } } ->
      match it with
      | (Const(Global,c) | App(Global,c,_,_)) when not @@ F.equal c F.rimplf -> F.Set.add c s
      | App(Global,ri,{ it = (Const(Global,c) | App(Global,c,_,_)) }, _) when F.equal ri F.rimplf -> F.Set.add c s
      (* | (Const _ | App _) -> s *)
      | _ -> assert false)
      F.Set.empty cl

  (* let rec append_body b1 b2 =
    match b1, b2 with
    | [], _ -> b2
    | [Scoped.Clauses c1], Scoped.Clauses c2 :: more ->
      Scoped.Clauses (c1 @ c2) :: more
    | x :: xs, _ -> x :: append_body xs b2 *)

  
  let compile_clause { Ast.Clause.body; attributes; loc } =
      { Ast.Clause.body = scope_loc_term body; attributes; loc }


  let compile_sequent { Ast.Chr.eigen; context; conclusion } =
    { Ast.Chr.eigen = scope_loc_term eigen; context = scope_loc_term context; conclusion = scope_loc_term conclusion }

  let compile_chr_rule { Ast.Chr.to_match; to_remove; guard; new_goal; attributes; loc } =
    let to_match = List.map compile_sequent to_match in
    let to_remove = List.map compile_sequent to_remove in
    let guard = Option.map scope_loc_term guard in
    let new_goal = Option.map compile_sequent new_goal in
    { Ast.Chr.to_match; to_remove; guard; new_goal; attributes; loc }

  let compile_kind kinds { Ast.Type.name; ty; loc } =
    let open Ast.TypeExpression in
    let rec count = function
      | TArr({ tit = TConst c },t) when c == F.typef -> 1 + count t.tit
      | TConst c when c == F.typef -> 0
      | x -> error ~loc "Syntax error: illformed kind.\nExamples:\nkind bool type.\nkind list type -> type.\n"
    in
    F.Map.add name (count ty.tit, loc) kinds  
    
  let run state p : State.t * Scoped.program =

    let rec compile_program omacros state { Ast.Structured.macros; kinds; types; type_abbrevs; modes; body } =
      (* check_no_overlap_macros omacros macros; *)
      let active_macros = F.Map.empty in
      (* let active_macros =
        List.fold_left compile_macro omacros macros in *)
      let type_abbrevs = List.map compile_type_abbrev type_abbrevs in
      let kinds = List.fold_left compile_kind F.Map.empty kinds in
      let types = List.fold_left (fun m t -> map_append t.Ast.Type.name (TypeList.make @@ compile_type t) m) F.Map.empty types in
      let modes = List.fold_left compile_mode F.Map.empty modes in
      let defs_m = defs_of_map modes in
      let defs_k = defs_of_map kinds in
      let defs_t = defs_of_map types in
      let defs_ta = defs_of_assoclist type_abbrevs in
      let state, kinds, types, type_abbrevs, modes, defs_b, body =
        compile_body active_macros kinds types type_abbrevs modes F.Set.empty state body in
      let symbols = F.Set.(union (union (union (union defs_k defs_m) defs_t) defs_b) defs_ta) in
      (state : State.t), active_macros,
      { Scoped.types; kinds; type_abbrevs; modes; body; symbols }

    and compile_body macros kinds types type_abbrevs (modes : (mode * Loc.t) F.Map.t) (defs : F.Set.t) state = function
      | [] -> state, kinds, types, type_abbrevs, modes, defs, []
      | Clauses cl :: rest ->
          let compiled_cl = List.map compile_clause cl in
          let defs = F.Set.union defs (global_hd_symbols_of_clauses compiled_cl) in
          let state, kinds, types, type_abbrevs, modes, defs, compiled_rest =
            compile_body macros kinds types type_abbrevs modes defs state rest in
          let compiled_rest =
            match compiled_rest with
            | Scoped.Clauses l :: rest -> Scoped.Clauses (compiled_cl @ l) :: rest
            | rest -> Scoped.Clauses compiled_cl :: rest in
          state, kinds, types, type_abbrevs, modes, defs, compiled_rest
      | Namespace (prefix, p) :: rest ->
          let prefix = F.show prefix in
          let state, _, p = compile_program macros state p in
          let state, kinds, types, type_abbrevs, modes, defs, compiled_rest =
            compile_body macros kinds types type_abbrevs modes defs state rest in
          let symbols = prepend [prefix] p.Scoped.symbols in
          state, kinds, types, type_abbrevs, modes, F.Set.union defs symbols,
          Scoped.Namespace(prefix, p) :: compiled_rest
      | Shorten(shorthands,p) :: rest ->
          let shorts = List.fold_left (fun s { Ast.Structured.short_name } ->
            F.Set.add short_name s) F.Set.empty shorthands in
          let state, _, p = compile_program macros state p in
          let state, kinds, types, type_abbrevs, modes, defs, compiled_rest =
            compile_body macros kinds types type_abbrevs modes defs state rest in
          state, kinds, types, type_abbrevs, modes,
          F.Set.union defs (F.Set.diff p.Scoped.symbols shorts),
          Scoped.Shorten(shorthands, p) :: compiled_rest
      | Constraints ({ctx_filter; clique; rules}, p) :: rest ->
          (* XXX missing check for nested constraints *)
          let rules = List.map compile_chr_rule rules in
          let state, _, p = compile_program macros state p in
          let state, kinds, types, type_abbrevs, modes, defs, compiled_rest =
            compile_body macros kinds types type_abbrevs modes defs state rest in
          state, kinds, types, type_abbrevs, modes,
          F.Set.union defs p.Scoped.symbols,
          Scoped.Constraints({ctx_filter; clique; rules},p) :: compiled_rest
      | Accumulated p :: rest ->
          let state, _, p = compile_program macros state p in
          let state, kinds, types, type_abbrevs, modes, defs, compiled_rest =
            compile_body macros kinds types type_abbrevs modes defs state rest in
          state, kinds, types, type_abbrevs, modes,
          F.Set.union defs p.Scoped.symbols,
          Scoped.Accumulated p :: compiled_rest
  
    in
    let state, toplevel_macros, pbody =
      compile_program F.Map.empty state p in
    state, { Scoped.pbody; toplevel_macros }

end

(* module ToDBL : sig
  open C

  (* Eliminates:
     - Locals: become the initial set of pi-quantified vars (local_names)
     - @macros
     - {{quatations}} (may add to the compiler state, later to be turned into
                       initial_state)

     Translates AST to preterm (terms where Arg(2) is represented with
     Const "%Arg2")
  *)

  val run : State.t -> toplevel_macros:(Ast.Term.t * Util.Loc.t) F.Map.t -> Ast.Structured.program -> State.t * Structured.program

  (* Exported since also used to flatten (here we "flatten" locals) *)
  val prefix_const : State.t -> string list -> C.t -> State.t * C.t
  val merge_modes : State.t -> (mode * Loc.t) Map.t -> (mode * Loc.t) Map.t -> (mode * Loc.t) Map.t
  val merge_types : State.t ->
    Types.types C.Map.t ->
    Types.types C.Map.t ->
    Types.types C.Map.t
  val merge_type_abbrevs : State.t ->
    type_abbrev_declaration C.Map.t ->
    type_abbrev_declaration C.Map.t ->
    type_abbrev_declaration C.Map.t

  (* Exported to compile the query *)
  val query_preterm_of_ast :
    depth:int -> macro_declaration -> State.t ->
      Loc.t * Ast.Term.t -> State.t * preterm
  val query_preterm_of_function :
    depth:int -> macro_declaration -> State.t ->
    (State.t -> State.t * (Loc.t * term) * Conversion.extra_goals) ->
      State.t * preterm

  (* Exported for quations *)
  val lp : QuotationHooks.quotation
  val is_Arg : State.t -> term -> bool
  val mk_Arg : State.t -> name:string -> args:term list -> State.t * term
  val get_Arg : State.t -> name:string -> args:term list -> term
  val get_Args : State.t -> term StrMap.t

  (* hack to implement read_term: it lets you call query compilation rutines
     at run time *)
  val temporary_compilation_at_runtime : (State.t -> 'b -> State.t * 'a) -> State.t -> 'b -> State.t * 'a

end = struct (* {{{ *)


(* **** ast->term compiler state ***************************************** *)

let todopp name _fmt _ = error ("pp not implemented for field: "^name)

let get_argmap, set_argmap, _update_argmap, drop_argmap =
  let argmap =
    State.declare
      ~name:"elpi:argmap" ~pp:(todopp "elpi:argmap")
      ~descriptor:D.elpi_state_descriptor
      ~clause_compilation_is_over:(fun _ -> empty_amap)
      ~goal_compilation_begins:(fun x -> x)
      ~goal_compilation_is_over:(fun ~args:_ _ -> None)
      ~compilation_is_over:(fun _ -> None)
      ~execution_is_over:(fun _ -> None)
     ~init:(fun () -> empty_amap) in
  State.(get argmap, set argmap, update_return argmap, drop argmap)

(* For bound variables *)
type varmap = term F.Map.t

let get_varmap, set_varmap, update_varmap, drop_varmap =
  let varmap : varmap State.component =
    State.declare
      ~name:"elpi:varmap" ~pp:(todopp "elpi:varmap")
      ~descriptor:D.elpi_state_descriptor
      ~clause_compilation_is_over:(fun x -> assert(F.Map.is_empty x); x)
      ~goal_compilation_begins:(fun x -> assert(F.Map.is_empty x); x)
      ~goal_compilation_is_over:(fun ~args:_ _ -> None)
      ~compilation_is_over:(fun _ -> None)
      ~execution_is_over:(fun _ -> None)
      ~init:(fun () -> F.Map.empty) in
  State.(get varmap, set varmap, update varmap, drop varmap)

(* Embed in the state everything, to cross quotations *)

type mtm = {
  macros : macro_declaration;
}

let get_mtm, set_mtm, drop_mtm =
  let mtm =
    State.declare
     ~name:"elpi:mtm" ~pp:(todopp "elpi:mtm")
     ~descriptor:D.elpi_state_descriptor
     ~clause_compilation_is_over:(fun _ -> None)
     ~goal_compilation_begins:(fun x -> x)
     ~goal_compilation_is_over:(fun ~args:_ _ -> None)
      ~compilation_is_over:(fun _ -> assert false)
      ~execution_is_over:(fun _ -> assert false)
      ~init:(fun () -> None) in
  State.(get mtm, set mtm, drop mtm)

let temporary_compilation_at_runtime f s x =
  let s = State.set D.while_compiling s true in
  let s = set_argmap s empty_amap in
  let s = set_varmap s F.Map.empty in
  let s = set_mtm s None in
  let s, x = f s x in
  let s = State.set D.while_compiling s false in
  s |> drop_argmap |> drop_varmap |> drop_mtm, x

(**** utils ******************)

let is_Arg state x =
  let { c2i } = get_argmap state in
  match x with
  | Const c -> C.Map.mem c c2i
  | App(c,_,_) -> C.Map.mem c c2i
  | _ -> false

let mk_Arg state ~name ~args =
  let state, (t, c) =
    let amap = get_argmap state in
    try state, StrMap.find name amap.n2t
    with Not_found ->
      let state, amap, tc = raw_mk_Arg state name amap in
      set_argmap state amap, tc in
  match args with
  | [] -> state, t
  | x::xs -> state, App(c,x,xs)

let get_Arg state ~name ~args =
  let { n2t } = get_argmap state in
  let t, c =
    try StrMap.find name n2t
    with Not_found -> error "get_Arg" in
  match args with
  | [] -> t
  | x::xs -> App(c,x,xs)

let fresh_Arg =
  let qargno = ref 0 in
  fun state ~name_hint:name ~args ->
    incr qargno;
    let name = Printf.sprintf "%s_%d_" name !qargno in
    mk_Arg state ~name ~args

let get_Args s = StrMap.map fst (get_argmap s).n2t

let is_discard f = F.(equal f dummyname) || (F.show f).[0] = '_'
let is_macro_name f = (F.show f).[0] = '@'


let preterm_of_ast loc ~depth:arg_lvl macro state ast =

  let spilling = ref false in
  let spy_spill c =
    spilling := !spilling || c == D.Global_symbols.spillc in

  let rec hcons_alien_term state = function
    | Term.Const x ->
        Symbols.get_global_or_allocate_bound_symbol state x
    | Term.Cons(x, y) ->
       let state, x = hcons_alien_term state x in
       let state, y = hcons_alien_term state y in
       state, Term.mkCons x y
    | Term.UVar _ | Term.AppUVar _ | Term.Arg _ | Term.AppArg _ -> assert false
    | Term.App(c,x,l) ->
       let state, x = hcons_alien_term state x in
       let state, l = map_acc hcons_alien_term state l in
       spy_spill c; state, Term.mkApp c x l
    | Term.Builtin(c,l) ->
       let state, l = map_acc hcons_alien_term state l in
       state, Term.mkBuiltin c l
    | Term.Lam x ->
       let state, x = hcons_alien_term state x in
       state, Term.mkLam x
    | (Term.Nil | Term.CData _ | Term.Discard) as x -> state, x
  in

  let rec stack_macro_of_ast lvl state f =
    try aux lvl state (fst (F.Map.find f macro))
    with Not_found -> error ~loc ("Undeclared macro " ^ F.show f)

  (* compilation of "functors" *)
  and stack_funct_of_ast curlvl state f =
    try state, F.Map.find f (get_varmap state)
    with Not_found ->
     if is_discard f then
       state, Discard
     else if F.is_uvar_name f then
       mk_Arg state ~name:(F.show f) ~args:[]
     else if is_macro_name f then
       stack_macro_of_ast curlvl state f
     else if Builtins.is_declared_str state (F.show f) then
       state, Builtin(fst(Symbols.get_global_symbol state f),[])
     else if CustomFunctorCompilation.is_backtick f then
       CustomFunctorCompilation.compile_backtick state f
     else if CustomFunctorCompilation.is_singlequote f then
       CustomFunctorCompilation.compile_singlequote state f
     else
       let state, (_,t) = Symbols.allocate_global_symbol state f in
       state, t

  and aux lvl state t =
    match t.Ast.Term.it with
    | Ast.Term.Const f when F.(equal f nilf) -> state, Term.Nil
    | Ast.Term.Const f -> stack_funct_of_ast lvl state f
    | Ast.Term.App({ Ast.Term.it = Ast.Term.Const f }, [hd;tl]) when F.(equal f consf) ->
       let state, hd = aux lvl state hd in
       let state, tl = aux lvl state tl in
       state, Term.Cons(hd,tl)
    | Ast.Term.App({ Ast.Term.it = Ast.Term.Const f }, tl) ->
       let state, rev_tl =
         List.fold_left (fun (state, tl) t ->
           let state, t = aux lvl state t in
           (state, t::tl))
          (state, []) tl in
       let tl = List.rev rev_tl in
       let state, c = stack_funct_of_ast lvl state f in
       begin match c with
       | Const c -> begin match tl with
          | hd2::tl -> spy_spill c; state, Term.App(c,hd2,tl)
          | _ -> anomaly "Application node with no arguments" end
       | App(c,hd1,tl1) -> spy_spill c; (* FG:decurrying: is this the right place for it? *)
          state, Term.App(c,hd1,tl1@tl)
       | Builtin(c,tl1) -> state, Term.Builtin(c,tl1@tl)
       | Lam _ -> (* macro with args *)
          hcons_alien_term state (R.deref_appuv ~from:lvl ~to_:lvl tl c)
       | Discard ->
          error ~loc "Clause shape unsupported: _ cannot be applied"
       | _ -> error ~loc "Clause shape unsupported" end
(*
    | Term.App (Term.Builtin f,tl) ->
       let cname = stack_custom_of_ast f in
       let state, rev_tl =
         List.fold_left (fun (state, tl) t ->
            let state, t = aux true lvl state t in
            (state, t::tl))
          (state, []) tl in
       state, Builtin(cname, List.rev rev_tl)
*)
    | Ast.Term.Lam (x,t) when F.(equal x dummyname)->
       let state, t' = aux (lvl+1) state t in
       state, Term.Lam t'
    | Ast.Term.Lam (x,t) ->
       let orig_varmap = get_varmap state in
       let state, c = Symbols.allocate_bound_symbol state lvl in
       let state = update_varmap state (F.Map.add x c) in
       let state, t' = aux (lvl+1) state t in
       set_varmap state orig_varmap, Term.Lam t'
    | Ast.Term.App ({ Ast.Term.it = Ast.Term.App (f,l1); loc },l2) ->
       aux lvl state ({ Ast.Term.it = Ast.Term.App (f, l1@l2); loc = Loc.merge t.Ast.Term.loc loc })
    | Ast.Term.CData c -> state, Term.CData (CData.hcons c)
    | Ast.Term.App ({ Ast.Term.it = Ast.Term.Lam _},_) ->
        error ~loc "Beta-redexes not allowed, use something like (F = x\\x, F a)"
    | Ast.Term.App ({ Ast.Term.it = Ast.Term.CData _},_) ->
        error ~loc "Applied literal"
    | Ast.Term.Quoted { Ast.Term.data; kind = None; qloc = loc } ->
         let unquote =
           let default_quotation = State.get default_quotation state in
           option_get ~err:"No default quotation" default_quotation in
         let state = set_mtm state (Some { macros = macro}) in
         begin try
           let state, t = unquote ~depth:lvl state loc data in
           hcons_alien_term state t
         with Elpi_parser.Parser_config.ParseError(loc,msg) -> error ~loc msg end
    | Ast.Term.Quoted { Ast.Term.data; kind = Some name; qloc = loc } ->
         let unquote =
           let named_quotations = State.get named_quotations state in
           try StrMap.find name named_quotations
           with Not_found -> anomaly ("No '"^name^"' quotation") in
         let state = set_mtm state (Some { macros = macro}) in
         begin try
           let state, t = unquote ~depth:lvl state loc data in
           hcons_alien_term state t
         with Elpi_parser.Parser_config.ParseError(loc,msg) -> error ~loc msg end
    | Ast.Term.App ({ Ast.Term.it = Ast.Term.Quoted _},_) ->
        error ~loc "Applied quotation"
  in

  (* arg_lvl is the number of local variables *)
  let state, t = aux arg_lvl state ast in
  state, t, !spilling
;;

let to_mode = function Ast.Mode.Input -> Input | Output -> Output

let type_expression_of_ast loc ~depth:arg_lvl macro state ast =

  let stack_funct_of_ast curlvl state f : State.t * ttype =
    try state, cons2tcons ~loc @@ F.Map.find f (get_varmap state)
    with Not_found ->
     if is_discard f then error ~loc "Discard operator cannot be used in type declaration"
     else if F.is_uvar_name f then 
        let state, t = mk_Arg state ~name:(F.show f) ~args:[] in
        state, cons2tcons ~loc t
     else if is_macro_name f then error ~loc "Macros cannot occur in types. Use a typeabbrev declaration instead"
     else
       let state, (c,_) = Symbols.allocate_global_symbol state f in
       state, TConst c in

  let rec aux lvl state : Ast.TypeExpression.t -> State.t * ttype = function
    | Ast.TypeExpression.TConst f -> stack_funct_of_ast lvl state f
    | TApp(f, hd, tl) ->
      let tl = hd :: tl in
      let state, rev_tl =
        List.fold_left (fun (state, tl) t ->
          let state, t = aux lvl state t in
          (state, t::tl))
        (state, []) tl in
      let tl = List.rev rev_tl in
      let state, c = stack_funct_of_ast lvl state f in
      begin match c with
      | TConst c -> begin match tl with
        | hd2::tl -> state, TApp(c,hd2,tl)
        | _ -> anomaly "Application node with no arguments" end
      | TApp(c,hd1,tl1) -> state, TApp(c,hd1,tl1@tl)
      | TLam _ -> error ~loc "Should be unreachable"
      | _ -> error ~loc "Clause shape unsupported" end
    | TCData c -> state, TCData (CData.hcons c)
    | TArr (a,b) -> 
      let state, a = aux lvl state a in
      let state, b = aux lvl state b in
      state, TArr(a, b)
    | TPred (_functional,l) -> (* TODO: @FissoreD _functionanlity should be taken into account *) 
      let rec aux' state = function
      | [] -> state, []
      | (m,t) :: xs -> 
          let state, t = aux lvl state t in
          let state, l = aux' state xs in
          state, ((to_mode m,t)::l) in
      let state, mode_type = aux' state l in
      state, TPred (false, mode_type) (* TODO: @FissoreD false should be replaced wrt _functional  *)
  in
  aux arg_lvl state ast

let typeabbrev_of_ast loc ~depth:depth macro state ast =
  let rec aux depth state = function
    | Ast.TypeAbbreviation.Lam (x, t) ->
       let orig_varmap = get_varmap state in
       let state, c = Symbols.allocate_bound_symbol state depth in
       let state = update_varmap state (F.Map.add x c) in
       let state, t = aux (depth+1) state t in
       set_varmap state orig_varmap, TLam t
    | Ty t -> type_expression_of_ast ~depth loc macro state t
  in
  aux depth state ast

let lp ~depth state loc s =
  let module P = (val option_get ~err:"No parser" (State.get parser state)) in
  let loc, ast = P.goal ~loc ~text:s in
  let macros =
    match get_mtm state with
    | None -> F.Map.empty
    | Some x -> x.macros in
  let state, t, _ = preterm_of_ast loc ~depth macros state ast in
  state, t

let prechr_rule_of_ast depth macros state r =
  let pcloc = r.Ast.Chr.loc in
  assert(is_empty_amap (get_argmap state));
  let intern state t = let state, t, _ = preterm_of_ast pcloc ~depth macros state t in state, t in
  let intern_sequent state { Ast.Chr.eigen; context; conclusion } =
    let state, peigen = intern state eigen in
    let state, pcontext = intern state context in
    let state, pconclusion = intern state conclusion in
    state, { peigen; pcontext; pconclusion } in
  let state, pto_match = map_acc intern_sequent state r.Ast.Chr.to_match in
  let state, pto_remove = map_acc intern_sequent state r.Ast.Chr.to_remove in
  let state, pguard = option_mapacc intern state r.Ast.Chr.guard in
  let state, pnew_goal = option_mapacc intern_sequent state r.Ast.Chr.new_goal in
  let pamap = get_argmap state in
  let state = State.end_clause_compilation state in
  let pname = r.Ast.Chr.attributes.Ast.Structured.cid in
  let pifexpr = r.Ast.Chr.attributes.Ast.Structured.cifexpr in
  state,
  { pto_match; pto_remove; pguard; pnew_goal; pamap; pname; pifexpr; pcloc }

(* used below *)
let preterms_of_ast loc ~depth macros state f t =
  assert(is_empty_amap (get_argmap state));
  let state, term, spilling = preterm_of_ast loc ~depth macros state t in
  let state, terms = f ~depth state term in
  let amap = get_argmap state in
  let state = State.end_clause_compilation state in
  (* TODO: may have spurious entries in the amap *)
  state, List.map (fun (loc,term) -> { term; amap; loc; spilling }) terms
;; 

let pretype_of_ast ~of_ast loc ~depth macros state t : State.t * pretype list =
  assert(is_empty_amap (get_argmap state));
  let state, term = of_ast loc ~depth macros state t in
  let tamap = get_argmap state in
  let state = State.end_clause_compilation state in
  state, List.map (fun (tloc,ttype) -> { ttype; tamap; tloc }) [loc,term]
;; 

let type_abbrev_of_ast = pretype_of_ast ~of_ast:typeabbrev_of_ast ;; 
let type_expression_of_ast = pretype_of_ast ~of_ast:type_expression_of_ast ;; 

(* exported *)
let query_preterm_of_function ~depth:_ macros state f =
  assert(is_empty_amap (get_argmap state));
  let state = set_mtm state (Some { macros }) in
  let state, (loc, main), gls = f state in
  let state, gls = Data.State.get Data.Conversion.extra_goals_postprocessing state gls state in
  let gls = List.map Data.Conversion.term_of_extra_goal gls in
  let term =
    match gls @ [main] with
    | [] -> assert false
    | [g] -> g
    | x :: xs -> mkApp D.Global_symbols.andc x xs in
  let amap = get_argmap state in
  state, { amap; term; loc; spilling = false }

let query_preterm_of_ast ~depth macros state (loc, t) =
  assert(is_empty_amap (get_argmap state));
  let state, term, spilling = preterm_of_ast loc ~depth macros state t in
  let amap = get_argmap state in
  state, { term; amap; loc; spilling }
;;

  open Ast.Structured

  let check_no_overlap_macros _ _ = ()

  let compile_macro m { Ast.Macro.loc; name = n; body } =
    if F.Map.mem n m then begin
      let _, old_loc = F.Map.find n m in
      error ~loc ("Macro "^F.show n^" declared twice:\n"^
             "first declaration: " ^ Loc.show old_loc ^"\n"^
             "second declaration: " ^ Loc.show loc)
    end;
    F.Map.add n (body,loc) m

  let compile_type_abbrev geti lcs state { Ast.TypeAbbreviation.name; nparams; loc; value } =
    let state, (taname, _) = Symbols.allocate_global_symbol state name in
    let state, tavalue = type_abbrev_of_ast loc ~depth:lcs F.Map.empty state value in
    let tavalue = assert(List.length tavalue = 1); List.hd tavalue in
    if tavalue.tamap.nargs != 0 then
      error ~loc ("type abbreviation for " ^ F.show name ^ " has unbound variables");
    state, { taname; tavalue; taparams = nparams; taloc = loc; timestamp = geti () }

  let add_to_index_type_abbrev state m ({ taname; taloc; tavalue; taparams } as x) =
    if C.Map.mem taname m then begin
      let { taloc = otherloc; tavalue = othervalue; taparams = otherparams } =
        C.Map.find taname m in
      if taparams != otherparams || othervalue.ttype <> tavalue.ttype then
      error ~loc:taloc
        ("duplicate type abbreviation for " ^ Symbols.show state taname ^
          ". Previous declaration: " ^ Loc.show otherloc)
    end;
    C.Map.add taname x m

  let compile_type lcs state { Ast.Type.attributes; loc; name; ty } =
    let state, (tname, _) = Symbols.allocate_global_symbol state name in
    let state, ttype = type_expression_of_ast loc ~depth:lcs F.Map.empty state ty in
    let ttype = assert(List.length ttype = 1); List.hd ttype in
    state, { Types.tindex = attributes; decl = { tname; ttype; tloc = loc } }

   let funct_of_ast state c =
     try
       match F.Map.find c (get_varmap state) with
       | Const x -> state, x
       | _ -> assert false
     with Not_found ->
       let state, (c,_) = Symbols.allocate_global_symbol state c in
       state, c

  let check_duplicate_mode state name (mode, loc) map =
    if C.Map.mem name map && fst (C.Map.find name map) <> mode then
      error ~loc
       ("Duplicate mode declaration for " ^ Symbols.show state name ^ " (also at "^
         Loc.show (snd (C.Map.find name map)) ^ ")")

  let rec to_mode_rec_aux = function
  | [] -> []
  | ((m: Ast.Mode.mode), Ast.TypeExpression.TPred (_,p)) :: l -> Ho (to_mode m, to_mode_rec_aux p) :: to_mode_rec_aux l 
  | (m, _) :: l -> Fo (to_mode m) :: to_mode_rec_aux l
  and to_mode_rec = function
    | Ast.TypeExpression.TConst _ | TCData _ -> []
    | TArr (a,b) -> []
    | TPred (_, m) -> to_mode_rec_aux m
    | TApp (a,b,l) -> []

  let compile_mode (state, modes) { Ast.Type.name; ty; loc } =
    let args = to_mode_rec ty in
    let state, mname = funct_of_ast state name in
    check_duplicate_mode state mname (args,loc) modes;
    state, C.Map.add mname (args,loc) modes

  let compile_functionality (state, (functionality: C.Set.t)) name =
    let state, mname = funct_of_ast state name in
    state, C.Set.add mname functionality

  let merge_modes state m1 m2 =
    if C.Map.is_empty m1 then m2 else
    C.Map.fold (fun k v m ->
      check_duplicate_mode state k v m;
      C.Map.add k v m)
    m2 m1
  let merge_types _s t1 t2 =
    C.Map.union (fun _ l1 l2 -> Some (Types.merge l1 l2)) t1 t2
  let merge_functionality m1 m2 = C.Set.union m1 m2

  let merge_type_abbrevs s m1 m2 =
    let len = C.Map.cardinal m1 in
    if C.Map.is_empty m2 then m1 else
    C.Map.fold (fun _ (k:type_abbrev_declaration) m -> add_to_index_type_abbrev s m {k with timestamp=k.timestamp+len}) m2 m1

  let rec toplevel_clausify loc ~depth state t =
    let state, cl = map_acc (pi2arg loc ~depth []) state (R.split_conj ~depth t) in
    state, List.concat cl
  and pi2arg loc ~depth acc state = function
    | App(c,Lam t,[]) when c == D.Global_symbols.pic ->
        let state, arg = fresh_Arg state ~name_hint:"X" ~args:[] in
        pi2arg loc ~depth (acc @ [arg]) state t
    | t ->
        if acc = [] then state, [loc, t]
        else toplevel_clausify loc state ~depth (R.subst ~depth acc t)

  let rec compile_clauses lcs state macros = function
    | [] -> lcs, state, []
    | { Ast.Clause.body; attributes; loc } :: rest ->
      let state, ts =
        preterms_of_ast loc ~depth:lcs macros state (toplevel_clausify loc) body in
      let cl = List.map (fun body -> { Ast.Clause.loc; attributes; body}) ts in
      let lcs, state, rest = compile_clauses lcs state macros rest in
      lcs, state, cl :: rest

  let compile_shorthand state { Ast.Structured.full_name; short_name; iloc } =
    let state, full_name = funct_of_ast state full_name in
    let state, short_name = funct_of_ast state short_name in
    state, { Ast.Structured.full_name; short_name; iloc }

  let rec append_body b1 b2 =
    match b1, b2 with
    | [], _ -> b2
    | [Structured.Clauses c1], Structured.Clauses c2 :: more ->
         Structured.Clauses (c1 @ c2) :: more
    | x :: xs, _ -> x :: append_body xs b2

  let defs_of_modes modes =
    C.Map.fold (fun k _ -> C.Set.add k) modes C.Set.empty

  let defs_of_types types =
    C.Map.fold (fun k _ s -> C.Set.add k s) types C.Set.empty

  let defs_of_type_abbrevs m =
    C.Map.fold (fun k _ acc -> C.Set.add k acc) m C.Set.empty

  let global_hd_symbols_of_clauses cl =
    List.fold_left (fun s { Ast.Clause.body = { term } } ->
      match term with
      | (Const c | App(c,_,_)) when c != D.Global_symbols.rimplc && c < 0 ->
           C.Set.add c s
      | App(ri,(Const c | App(c,_,_)), _) when ri == D.Global_symbols.rimplc && c < 0 ->
           C.Set.add c s
      | (Const _ | App _) -> s
      | Builtin(c,_) -> C.Set.add c s
      | _ -> assert false)
      C.Set.empty cl

  let namespace_separator = "."

  let prefix_const state prefix c =
      Symbols.allocate_global_symbol_str state
        (String.concat namespace_separator prefix ^
                      namespace_separator ^
                      Symbols.show state c)

  let prepend state p s =
    let res = ref C.Set.empty in
    let state = C.Set.fold
      (fun x state ->
         let state, c = prefix_const state [p] x in
         res := C.Set.add c !res;
         state)
      s
      state in
    state, !res


  let map_append k v m =
    try
      let l = C.Map.find k m in
      C.Map.add k (Types.append v l) m
    with Not_found ->
      C.Map.add k (Types.make v) m

  let run (state : State.t) ~toplevel_macros p =
    let geti = let i = ref ~-1 in fun () -> incr i; !i in
 (* FIXME: otypes omodes - NO, rewrite spilling on data.term *)
    let rec compile_program omacros lcs state { macros; types; type_abbrevs; modes; body; functionality } =
      check_no_overlap_macros omacros macros;
      let active_macros =
        List.fold_left compile_macro omacros macros in
      let state, type_abbrevs = map_acc (compile_type_abbrev geti lcs) state type_abbrevs in
      let type_abbrevs = List.fold_left (add_to_index_type_abbrev state) C.Map.empty type_abbrevs in
      let state, types =
        map_acc (compile_type lcs) state types in
      let types = List.fold_left (fun m t -> map_append t.Types.decl.tname t m) C.Map.empty types in
      let state, (modes:(Data.mode * Loc.t) C.Map.t) = List.fold_left compile_mode (state,C.Map.empty) modes in
      let state, functionality = List.fold_left compile_functionality (state,C.Set.empty) functionality in
      let defs_m = defs_of_modes modes in
      let defs_t = defs_of_types types in
      let defs_ta = defs_of_type_abbrevs type_abbrevs in
      let lcs, state, types, type_abbrevs, modes, defs_b, body =
        compile_body active_macros types type_abbrevs modes lcs C.Set.empty state body in
      let symbols = C.Set.(union (union (union defs_m defs_t) defs_b) defs_ta) in
      (state : State.t), lcs, active_macros,
      { Structured.types; type_abbrevs; modes; functionality; body; symbols }

    and compile_body macros types type_abbrevs (modes: (Data.mode * Loc.t) C.Map.t) lcs defs state = function
      | [] -> lcs, state, types, type_abbrevs, modes, defs, []
      | Locals (nlist, p) :: rest ->
          let orig_varmap = get_varmap state in
          let lcs, state =
            List.fold_left (fun (lcs,state) name ->
              let state, rel = Symbols.allocate_bound_symbol state lcs in
              lcs+1, update_varmap state (F.Map.add name rel))
            (lcs,state) nlist in
          let state, lcs, _,
            { Structured.types = tp; type_abbrevs = ta; modes = mp; body; symbols }
            =
            compile_program macros lcs state p in
          let defs = C.Set.union defs symbols in
          let modes = merge_modes state modes mp in
          let types = merge_types state types tp in
          let type_abbrevs = merge_type_abbrevs state type_abbrevs ta in
          let state = set_varmap state orig_varmap in
          let lcs, state, types, type_abbrevs, modes, defs, compiled_rest =
            compile_body macros types type_abbrevs modes lcs defs state rest in
          lcs, state, types, type_abbrevs, modes, defs, append_body body compiled_rest
      | Clauses cl :: rest ->
          let lcs, state, compiled_cl = compile_clauses lcs state macros cl in
          let compiled_cl = List.concat compiled_cl in
          let defs =
            C.Set.union defs (global_hd_symbols_of_clauses compiled_cl) in
          let compiled_cl = [Structured.Clauses compiled_cl] in
          let lcs, state, types, type_abbrevs, modes, defs, compiled_rest =
            compile_body macros types type_abbrevs modes lcs defs state rest in
          lcs, state, types, type_abbrevs, modes, defs, append_body compiled_cl compiled_rest
      | Namespace (prefix, p) :: rest ->
          let prefix = F.show prefix in
          let state, lcs, _, p = compile_program macros lcs state p in
          let lcs, state, types, type_abbrevs, modes, defs, compiled_rest =
            compile_body macros types type_abbrevs modes lcs defs state rest in
          let state, symbols = prepend state prefix p.Structured.symbols in
          lcs, state, types, type_abbrevs, modes, C.Set.union defs symbols,
          Structured.Namespace(prefix, p) :: compiled_rest
      | Shorten(shorthands,p) :: rest ->
          let state, shorthands = map_acc compile_shorthand state shorthands in
          let shorts = List.fold_left (fun s { short_name } ->
            C.Set.add short_name s) C.Set.empty shorthands in
          let state, lcs, _, p = compile_program macros lcs state p in
          let lcs, state, types, type_abbrevs, modes, defs, compiled_rest =
            compile_body macros types type_abbrevs modes lcs defs state rest in
          lcs, state, types, type_abbrevs, modes,
          C.Set.union defs (C.Set.diff p.Structured.symbols shorts),
          Structured.Shorten(shorthands, p) :: compiled_rest
      | Constraints ({ctx_filter; clique; rules}, p) :: rest ->
          (* XXX missing check for nested constraints *)
          let state, clique = map_acc funct_of_ast state clique in
          let state, ctx_filter = map_acc funct_of_ast state ctx_filter in
          let state, rules =
            map_acc (prechr_rule_of_ast lcs macros) state rules in
          let state, lcs, _, p = compile_program macros lcs state p in
          let lcs, state, types, type_abbrevs, modes, defs, compiled_rest =
            compile_body macros types type_abbrevs modes lcs defs state rest in
          lcs, state, types, type_abbrevs, modes,
          C.Set.union defs p.Structured.symbols,
          Structured.Constraints({ctx_filter; clique; rules},p) :: compiled_rest
    in
    let state, local_names, toplevel_macros, pbody =
      compile_program toplevel_macros 0 state p in
    state, { Structured.local_names; pbody; toplevel_macros }

end (* }}} *)

let lp = ToDBL.lp
let is_Arg = ToDBL.is_Arg
let mk_Arg = ToDBL.mk_Arg
let get_Args = ToDBL.get_Args
let get_Arg = ToDBL.get_Arg *)

(*
module Flatten : sig

  (* Eliminating the structure (name spaces) *)

  val run : State.t -> Structured.program -> C.Set.t * macro_declaration * Flat.program

  val relocate : State.t -> D.constant D.Constants.Map.t -> Flat.program  -> Flat.program
  val relocate_term : State.t -> D.constant D.Constants.Map.t -> term -> term

end = struct (* {{{ *)


  open Structured

  (* This function *must* re-hashcons all leaves (Const) and recognize
     builtins since it is (also) used to apply a compilation unit relocation *)

  let smart_map_term state f t =
    let rec aux_sm = function
      | Const c ->
          let c1 = f c in
          if Builtins.is_declared state c1 then Builtin(c1,[])
          else Symbols.get_canonical state c1
      | Lam t as x ->
          let t1 = aux_sm t in
          if t == t1 then x else Lam t1
      | AppArg(i,ts) as x ->
          let ts1 = smart_map aux_sm ts in
          if ts == ts1 then x else AppArg(i,ts1)
      | AppUVar(r,lvl,ts) as x ->
          assert(!!r == D.dummy);
          let ts1 = smart_map aux_sm ts in
          if ts == ts1 then x else AppUVar(r,lvl,ts1)
      | Builtin(c,ts) ->
          let c1 = f c in
          let ts1 = smart_map aux_sm ts in
          if Builtins.is_declared state c1 then Builtin(c,ts1)
          else if ts1 = [] then Symbols.get_canonical state c1 else App(c,List.hd ts1,List.tl ts1)
      | App(c,t,ts) ->
          let c1 = f c in
          let t1 = aux_sm t in
          let ts1 = smart_map aux_sm ts in
          if Builtins.is_declared state c1 then Builtin (c1,t1 :: ts1)
          else App(c1,t1,ts1)
      | Cons(hd,tl) as x ->
          let hd1 = aux_sm hd in
          let tl1 = aux_sm tl in
          if hd == hd1 && tl == tl1 then x else Cons(hd1,tl1)
      | UVar(r,_,_) as x ->
          assert(!!r == D.dummy);
          x
      | (Arg _ | CData _ | Nil | Discard) as x -> x
    in
      aux_sm t

  let smart_map_ttype state f t =
    let rec aux_sm = function
      | TConst c -> cons2tcons @@ Symbols.get_canonical state (f c)
      | TLam t as x ->
          let t1 = aux_sm t in
          if t == t1 then x else TLam t1
      | TApp(c,t,ts) ->
          let c1 = f c in
          let t1 = aux_sm t in
          let ts1 = smart_map aux_sm ts in
          TApp(c1,t1,ts1)
      | TCData _ as x -> x
      | TArr (a,b) -> TArr (aux_sm a, aux_sm b)
      | TPred (f, l) -> TPred (f, List.map (fun (m, t) -> m, aux_sm t) l)
    in
      aux_sm t

let subst_amap state f { nargs; c2i; i2n; n2t; n2i } =
  let c2i = Constants.Map.fold (fun k v m -> Constants.Map.add (f k) v m) c2i Constants.Map.empty in
  let n2t = StrMap.map (fun (t,c) ->
    let c = f c in
    let t = match t with
      | Const c -> Symbols.get_canonical state (f c)
      | _ -> assert false in
    t,c) n2t in
  { nargs; c2i; i2n; n2t; n2i }

  let smart_map_type state f ({ Types.tindex; decl = { tname; ttype; tloc }} as tdecl) =
    let tname1 = f tname in
    let ttype1 = smart_map_ttype state f ttype.ttype in
    let tamap1 =subst_amap state f ttype.tamap in
    if tname1 == tname && ttype1 == ttype.ttype && ttype.tamap = tamap1 then tdecl
    else { Types.tindex; decl = { tname = tname1; tloc; ttype = { ttype = ttype1; tamap = tamap1; tloc = ttype.tloc; } } }


  let map_sequent state f { peigen; pcontext; pconclusion } =
    {
      peigen = smart_map_term state f peigen;
      pcontext = smart_map_term state f pcontext;
      pconclusion =smart_map_term state f pconclusion;
    }

  let map_chr state f
    { pto_match; pto_remove; pguard; pnew_goal; pamap; pifexpr; pname; pcloc }
  =
    {
      pto_match = smart_map (map_sequent state f) pto_match;
      pto_remove = smart_map (map_sequent state f) pto_remove;
      pguard = option_map (smart_map_term state f) pguard;
      pnew_goal = option_map (map_sequent state f) pnew_goal;
      pamap = subst_amap state f pamap;
      pifexpr; pname; pcloc;
    }

  let smart_map_preterm state f ({ term; amap; loc; spilling } as x) =
    let term1 = smart_map_term state f term in
    let amap1 = subst_amap state f amap in
    if term1 == term && amap1 == amap then x
    else { term = term1; amap = amap1; loc; spilling }

  let smart_map_pretype state f ({ ttype; tamap; tloc } as x) =
    let term1 = smart_map_ttype state f ttype in
    let amap1 = subst_amap state f tamap in
    if term1 == ttype && amap1 == tamap then x
    else { ttype = term1; tamap = amap1; tloc }

  let map_clause state f ({ Ast.Clause.body } as x) =
    let body1 = smart_map_preterm state f body in
    if body1 == body then x else { x with Ast.Clause.body = body1 }

  type subst = (string list * C.t C.Map.t)


  let apply_subst (f : C.t C.Map.t -> 'a -> 'a) (s : subst) : 'a -> 'a =
    fun x -> f (snd s) x

  let _apply_subst_list f = apply_subst (fun x -> smart_map (f x))

  let tabbrevs_map state f m =
    C.Map.fold (fun _ { taname; tavalue; taparams; taloc; timestamp } m ->
      (* TODO: check for collisions *)
      let taname = f taname in
      let tavalue = smart_map_pretype state f tavalue in
      C.Map.add taname { taname; tavalue; taparams; taloc; timestamp } m
      ) m C.Map.empty

  let apply_subst_constant ?live_symbols =
    apply_subst (fun m x ->
      let x = try C.Map.find x m with Not_found -> x in
      begin match live_symbols with None -> () | Some r -> r := C.Set.add x !r end;
      x)

  let apply_subst_types ?live_symbols st s tm =
    let ksub = apply_subst_constant ?live_symbols s in
    C.Map.fold (fun k tl m -> C.Map.add (ksub k) (Types.smart_map (smart_map_type st ksub) tl) m) tm C.Map.empty

  let apply_subst_type_abbrevs ?live_symbols st s = tabbrevs_map st (apply_subst_constant ?live_symbols s)

  let apply_subst_modes ?live_symbols s m =
    C.Map.fold (fun c v m -> C.Map.add (apply_subst_constant ?live_symbols s c) v m) m C.Map.empty
    
  let apply_subst_functionality ?live_symbols s f =
    C.Set.fold (fun c m -> C.Set.add (apply_subst_constant ?live_symbols s c) m) f C.Set.empty

  let apply_subst_chr ?live_symbols st s (l: (block_constraint)) =
    let app_sub_const f = smart_map (f (apply_subst_constant ?live_symbols s)) in
     (fun {ctx_filter; rules; clique} ->
        { ctx_filter = app_sub_const Fun.id ctx_filter;
          clique = app_sub_const Fun.id clique;
          rules = app_sub_const (map_chr st) rules }) l

  let apply_subst_clauses ?live_symbols st s =
    smart_map (map_clause st (apply_subst_constant ?live_symbols s))

  let push_subst state extra_prefix symbols_affected (oldprefix, oldsubst) =
    let newprefix = oldprefix @ [extra_prefix] in
    let state, newsubst =
      C.Set.fold (fun c (state,subst) ->
        let state, c1 = ToDBL.prefix_const state newprefix c in
        state, C.Map.add c c1 subst) symbols_affected (state, oldsubst) in
    state, (newprefix, newsubst)

  let push_subst_shorthands shorthands _symbols_defined (oldprefix, oldsubst) =
    let push1 m { Ast.Structured.short_name; full_name } =
      C.Map.add short_name
        (try C.Map.find full_name m with Not_found -> full_name) m
    in
    oldprefix, List.fold_left push1 oldsubst shorthands

  let rec compile_body live_symbols state lcs types type_abbrevs modes clauses chr subst bl =
    match bl with
    | [] -> types, type_abbrevs, modes, clauses, chr
    | Shorten(shorthands, { types = t; type_abbrevs = ta; modes = m; body; symbols = s }) :: rest ->
        let insubst = push_subst_shorthands shorthands s subst in
        let types = ToDBL.merge_types state (apply_subst_types ~live_symbols state insubst t) types in
        let type_abbrevs = ToDBL.merge_type_abbrevs state type_abbrevs (apply_subst_type_abbrevs ~live_symbols state insubst ta) in
        let modes = ToDBL.merge_modes state (apply_subst_modes ~live_symbols insubst m) modes in
        let types, type_abbrevs, modes, clauses, chr =
          compile_body live_symbols state lcs types type_abbrevs modes clauses chr insubst body in
        compile_body live_symbols state lcs types type_abbrevs modes clauses chr subst rest
    | Namespace (extra, { types = t; type_abbrevs = ta; modes = m; body; symbols = s }) :: rest ->
        let state, insubst = push_subst state extra s subst in
        let types = ToDBL.merge_types state (apply_subst_types ~live_symbols state insubst t) types in
        let type_abbrevs = ToDBL.merge_type_abbrevs state type_abbrevs (apply_subst_type_abbrevs ~live_symbols state insubst ta) in
        let modes = ToDBL.merge_modes state (apply_subst_modes ~live_symbols insubst m) modes in
        let types, type_abbrevs, modes, clauses, chr =
          compile_body live_symbols state lcs types type_abbrevs modes clauses chr insubst body in
        compile_body live_symbols state lcs types type_abbrevs modes clauses chr subst rest
    | Clauses cl :: rest ->
        let cl = apply_subst_clauses ~live_symbols state subst cl in
        let clauses = clauses @ cl in
        compile_body live_symbols state lcs types type_abbrevs modes clauses chr subst rest
    | Constraints ({ctx_filter; clique; rules}, { types = t; type_abbrevs = ta; modes = m; body }) :: rest ->
        let types = ToDBL.merge_types state (apply_subst_types ~live_symbols state subst t) types in
        let type_abbrevs = ToDBL.merge_type_abbrevs state type_abbrevs (apply_subst_type_abbrevs ~live_symbols state subst ta) in
        let modes = ToDBL.merge_modes state (apply_subst_modes ~live_symbols subst m) modes in
        let chr = apply_subst_chr ~live_symbols state subst {ctx_filter;clique;rules} :: chr in
        let types, type_abbrevs, modes, clauses, chr =
          compile_body live_symbols state lcs types type_abbrevs modes clauses chr subst body in
        compile_body live_symbols state lcs types type_abbrevs modes clauses chr subst rest

  let run state
    { Structured.local_names;
      pbody = { types; type_abbrevs; modes; body; functionality; symbols = _ };
      toplevel_macros;
    }
  =
    let live_symbols = ref C.Set.empty in
    let empty_subst = [],C.Map.empty in
    (* appying a subst also computes live symbols *)
    let types = apply_subst_types ~live_symbols state empty_subst types in
    let type_abbrevs = apply_subst_type_abbrevs ~live_symbols state empty_subst type_abbrevs in
    let modes = apply_subst_modes ~live_symbols empty_subst modes in
    let types, type_abbrevs, modes, clauses, chr =
      compile_body live_symbols state local_names types type_abbrevs modes [] [] empty_subst body in
    !live_symbols, toplevel_macros, { Flat.types;
      type_abbrevs;
      modes;
      clauses;
      chr = List.rev chr;
      local_names;
    }
    let relocate_term state s t =
      let ksub = apply_subst_constant ([],s) in
      smart_map_term state ksub t

    let relocate state f {
      Flat.types;
      type_abbrevs;
      modes;
      clauses;
      chr;
      local_names;
    } =
      let f = [], f in
    {
      Flat.types = apply_subst_types state f types;
      type_abbrevs = apply_subst_type_abbrevs state f type_abbrevs;
      modes = apply_subst_modes f modes;
      clauses = apply_subst_clauses state f clauses;
      chr = smart_map (apply_subst_chr state f) chr;
      local_names;
    }



end (* }}} *)
 *)

 module Flatten : sig

  (* Eliminating the structure (name spaces) *)

  val run : State.t -> Scoped.program -> Flat.program
  val merge_modes :
    (mode * Loc.t) F.Map.t ->
    (mode * Loc.t) F.Map.t ->
    (mode * Loc.t) F.Map.t
  val merge_kinds :
    Arity.t F.Map.t ->
    Arity.t F.Map.t ->
    Arity.t F.Map.t
  (* val merge_types :
    TypeList.t F.Map.t ->
    TypeList.t F.Map.t ->
    TypeList.t F.Map.t *)
  val merge_type_assignments :
    TypeAssignment.overloaded_skema F.Map.t ->
    TypeAssignment.overloaded_skema F.Map.t ->
    TypeAssignment.overloaded_skema F.Map.t
  val merge_type_abbrevs :
    (F.t * ScopedTypeExpression.t) list ->
    (F.t * ScopedTypeExpression.t) list ->
    (F.t * ScopedTypeExpression.t) list

 end = struct

  type subst = { old_prefix : string list; subst : F.t F.Map.t }

  let empty_subst = { old_prefix = []; subst = F.Map.empty }

  let push_subst extra_prefix symbols_affected { old_prefix; subst = oldsubst } =
    let new_prefix = old_prefix @ [extra_prefix] in
    let newsubst =
      F.Set.fold (fun c subst ->
        let c1 = prefix_const new_prefix c in
       F.Map.add c c1 subst) symbols_affected oldsubst in
    { old_prefix = new_prefix; subst = newsubst }

  let push_subst_shorthands shorthands { old_prefix; subst = oldsubst } =
    let push1 m { Ast.Structured.short_name; full_name } =
      F.Map.add short_name
        (try F.Map.find full_name m with Not_found -> full_name) m
    in
      { old_prefix; subst = List.fold_left push1 oldsubst shorthands }


  let smart_map_scoped_term f t =
    let open ScopedTerm in
    let rec aux it =
      match it with
      | Const(Local,_) -> it
      | Const(Global,c) -> let c' = f c in if c == c' then it else Const(Global,c')
      | Spill(t,n) -> let t' = aux_loc t in if t' == t then it else Spill(t',n)
      | App(scope,c,x,xs) ->
          let c' = if scope = Global then f c else c in
          let x' = aux_loc x in
          let xs' = smart_map aux_loc xs in
          if c == c' && x == x' && xs == xs' then it
          else App(scope,c',x',xs')
      | Lam(n,b) ->
          let b' = aux_loc b in
          if b == b' then it else Lam(n,b')
      | Var(c,l) ->
          let l' = smart_map aux_loc l in
          if l == l' then it else Var(c,l')
      | Discard -> it
      | CData _ -> it
    and aux_loc ({ it; loc; ty } as orig) =
      let it' = aux it in
      if it == it' then orig
      else { it = it'; loc; ty }
    in
      aux_loc t

  let smart_map_clause f ({ Ast.Clause.body } as x) =
    let body' = f body in
    if body == body' then x else { x with body = body' }

  let subst_global { subst = s } f =
    try F.Map.find f s
    with Not_found -> f

  let apply_subst_clauses s cl =
    smart_map (smart_map_clause (smart_map_scoped_term (subst_global s))) cl

  let smart_map_sequent f ({ Ast.Chr. eigen; context; conclusion } as orig) =
    let eigen' = smart_map_scoped_term f eigen in
    let context' = smart_map_scoped_term f context in
    let conclusion' = smart_map_scoped_term f conclusion in
    if eigen' == eigen && context' == context && conclusion' == conclusion then orig
    else { Ast.Chr.eigen = eigen'; context = context'; conclusion = conclusion' }

  let smart_map_chr f ({ Ast.Chr.to_match; to_remove; guard; new_goal; attributes; loc } as orig) =
    let to_match' = smart_map (smart_map_sequent f) to_match in
    let to_remove' = smart_map (smart_map_sequent f) to_remove in
    let guard' = Util.option_map (smart_map_scoped_term f) guard in
    let new_goal' = Util.option_map (smart_map_sequent f) new_goal in
    if to_match' == to_match && to_remove' == to_remove && guard' == guard && new_goal' == new_goal then orig
    else { Ast.Chr.to_match = to_match'; to_remove = to_remove'; guard = guard'; new_goal = new_goal'; attributes; loc }

  let smart_map_chrs f ({ Ast.Structured.clique; ctx_filter; rules } as orig) =
    let clique' = smart_map f clique in
    let ctx_filter' = smart_map f ctx_filter in
    let rules' = smart_map (smart_map_chr f) rules in
    if clique' == clique && ctx_filter' == ctx_filter && rules' == rules then orig
    else { Ast.Structured.clique = clique'; ctx_filter = ctx_filter'; rules = rules' }

  let apply_subst_chrs s = smart_map_chrs (subst_global s)


  let apply_subst_types s = TypeList.smart_map (ScopedTypeExpression.smart_map (subst_global s))

  let apply_subst_types s l =
    F.Map.fold (fun k v m -> F.Map.add (subst_global s k) (apply_subst_types s v) m) l F.Map.empty


  let apply_subst_modes s l =
    F.Map.fold (fun k v m -> F.Map.add (subst_global s k) v m) l F.Map.empty

  let apply_subst_kinds s l =
    F.Map.fold (fun k v m -> F.Map.add (subst_global s k) v m) l F.Map.empty
  
  let apply_subst_type_abbrevs s l =
    List.map (fun (k, v) -> subst_global s k, ScopedTypeExpression.smart_map (subst_global s) v) l

    let merge_type_assignments t1 t2 =
      F.Map.union (fun _ l1 l2 -> Some (TypeAssignment.merge_skema l1 l2)) t1 t2

    let merge_types t1 t2 =
      F.Map.union (fun _ l1 l2 -> Some (TypeList.merge l1 l2)) t1 t2
  
    let merge_modes m1 m2 =
      if F.Map.is_empty m1 then m2 else
      F.Map.fold (fun k v m ->
        Scope_Quotation_Macro.check_duplicate_mode k v m;
        F.Map.add k v m)
      m2 m1

    let merge_kinds t1 t2 =
        F.Map.union (fun f (k,loc1 as kdecl) (k',loc2) ->
          if k == k' then Some kdecl else error ~loc:loc2 ("Duplicate kind declaration for " ^ F.show f ^ ". Previously declared in " ^ Loc.show loc1);
          ) t1 t2
  

    let add_to_index_type_abbrev m ({ ScopedTypeExpression.name; loc; value; nparams } as x) =
      if F.Map.mem name m then begin
        let { ScopedTypeExpression.loc = otherloc; value = othervalue; nparams = otherparams } =
          F.Map.find name m in
        if nparams != otherparams || not @@ ScopedTypeExpression.eq (ScopeContext.empty ()) othervalue value then
        error ~loc
          ("duplicate type abbreviation for " ^ F.show name ^
            ". Previous declaration: " ^ Loc.show otherloc)
      end;
      F.Map.add name x m


    let merge_type_abbrevs m1 m2 = m1 @ m2 (* TODO check duplicates *)

  let rec compile_block kinds types type_abbrevs modes clauses chr subst = function
    | [] -> kinds, types, type_abbrevs, modes, clauses, chr
    | Scoped.Shorten(shorthands, { kinds = k; types = t; type_abbrevs = ta; modes = m; body; symbols = _ }) :: rest ->
      let insubst = push_subst_shorthands shorthands subst in
      let kinds = merge_kinds (apply_subst_kinds insubst k) kinds in
      let types = merge_types (apply_subst_types insubst t) types in
      let type_abbrevs = merge_type_abbrevs type_abbrevs (apply_subst_type_abbrevs insubst ta) in
      let modes = merge_modes (apply_subst_modes insubst m) modes in
      let kinds, types, type_abbrevs, modes, clauses, chr =
        compile_block kinds types type_abbrevs modes clauses chr insubst body in
      compile_block kinds types type_abbrevs modes clauses chr subst rest
  | Scoped.Namespace (extra, { kinds = k; types = t; type_abbrevs = ta; modes = m; body; symbols = s }) :: rest ->
      let new_subst = push_subst extra s subst in
      let kinds = merge_kinds (apply_subst_kinds new_subst k) kinds in
      let types = merge_types (apply_subst_types new_subst t) types in
      let type_abbrevs = merge_type_abbrevs type_abbrevs (apply_subst_type_abbrevs new_subst ta) in
      let modes = merge_modes (apply_subst_modes new_subst m) modes in
      let kinds, types, type_abbrevs, modes, clauses, chr =
        compile_block kinds types type_abbrevs modes clauses chr new_subst body in
      compile_block kinds types type_abbrevs modes clauses chr subst rest
  | Scoped.Clauses cl :: rest ->
      let cl = apply_subst_clauses subst cl in
      let clauses = cl :: clauses in
      compile_block kinds types type_abbrevs modes clauses chr subst rest
  | Scoped.Constraints (ch, { kinds = k; types = t; type_abbrevs = ta; modes = m; body }) :: rest ->
      let kinds = merge_kinds (apply_subst_kinds subst k) kinds in
      let types = merge_types (apply_subst_types subst t) types in
      let type_abbrevs = merge_type_abbrevs type_abbrevs (apply_subst_type_abbrevs subst ta) in
      let modes = merge_modes (apply_subst_modes subst m) modes in
      let chr = apply_subst_chrs subst ch :: chr in
      let kinds, types, type_abbrevs, modes, clauses, chr =
        compile_block kinds types type_abbrevs modes clauses chr subst body in
      compile_block kinds types type_abbrevs modes clauses chr subst rest
  | Scoped.Accumulated { kinds=k; types = t; type_abbrevs = ta; modes = m; body; symbols = _ } :: rest ->
      let kinds = merge_kinds (apply_subst_kinds subst k) kinds in
      let types = merge_types (apply_subst_types subst t) types in
      let type_abbrevs = merge_type_abbrevs type_abbrevs (apply_subst_type_abbrevs subst ta) in
      let modes = merge_modes (apply_subst_modes subst m) modes in
      let kinds, types, type_abbrevs, modes, clauses, chr =
        compile_block kinds types type_abbrevs modes clauses chr subst body in
      compile_block kinds types type_abbrevs modes clauses chr subst rest

  let compile_body { Scoped.kinds; types; type_abbrevs; modes; symbols; body } =
    compile_block kinds types type_abbrevs modes [] [] empty_subst body

  let run state { Scoped.pbody; toplevel_macros } =
    let kinds, types, type_abbrevs, modes, clauses_rev, chr_rev = compile_body pbody in
    { Flat.kinds; types; type_abbrevs; modes; clauses = List.(flatten (rev clauses_rev)); chr = List.rev chr_rev; toplevel_macros; builtins = [] } (* TODO builtins can be in a unit *)


end
(* 
module Spill : sig

  (* Eliminate {func call} *)


  val spill_clause :
    State.t -> types:Types.types C.Map.t -> modes:(constant -> mode) ->
      (preterm, 'a) Ast.Clause.t -> (preterm, 'a) Ast.Clause.t

  val spill_chr :
    State.t -> types:Types.types C.Map.t -> modes:(constant -> mode) ->
      block_constraint -> block_constraint

  (* Exported to compile the query *)
  val spill_preterm :
    State.t -> Types.types C.Map.t -> (C.t -> mode) -> preterm -> preterm

end = struct (* {{{ *)

  type typespill =
    | Variadic of typespill * typespill 
    | Arrow of typespill list * typespill | Prop | Unknown
    [@@deriving show]

  let rec read_ty = function
    | TApp(c,x,[y]) when c == D.Global_symbols.variadic -> Variadic (read_ty x,read_ty y)
    | TArr(x,y) -> 
        let ty_x = read_ty x in
        begin match read_ty y with
        | Arrow(tys,ty) -> Arrow (ty_x :: tys, ty)
        | ty -> Arrow([ty_x], ty) end
    | TConst x when x == D.Global_symbols.propc -> Prop
    | TPred (_, l) -> Arrow (List.map (fun (_, t) -> read_ty t) l, Prop)
    | _ -> Unknown

  let type_of_const ~state types c =
    try
      let { Types.decl = { ttype } } = (C.Map.find c types).Types.def in
      read_ty ttype.ttype
    with Not_found -> Unknown

  let missing_args_of state loc modes types t =
    let c, args =
      let rec aux_mia = function
        | App (c,_,[x]) when c == D.Global_symbols.implc -> aux_mia x
        | App (c,x,xs) when c == D.Global_symbols.andc ->
            aux_mia List.(hd (rev (x :: xs)))
        | App (c,x,xs) -> c, x :: xs
        | Const c -> c, []
        | Builtin(c,args) -> c, args
        | _ -> error ~loc "Only applications can be spilled"
      in
        aux_mia t in
    let ty = type_of_const state types c in
    let ty_mode, mode =
      match modes c with
      | l -> `Arrow(List.length l,Prop), l
      | exception Not_found -> `Unknown, [] in
    let nargs = List.length args in
    let missing_args =
      match ty_mode, ty with
      | `Unknown,Arrow(args,_) -> List.length args - nargs
      | `Arrow(arity,_),_ ->
          let missing = arity - nargs in
          let output_suffix =
            let rec aux_output = function x :: l when get_arg_mode x = Output -> 1 + aux_output l | _ -> 0 in
            aux_output (List.rev mode) in
          if missing > output_suffix then
            error ~loc Printf.(sprintf
              "Cannot spill %s: only %d out of %d missing arguments are output"
              (Symbols.show state c) output_suffix missing);
          missing
      | _ -> error ~loc ("Cannot spill: unknown arity of " ^ Symbols.show state c) in
    if missing_args <= 0 then
      error ~loc ("Cannot spill: " ^ Symbols.show state c ^ " is fully applied");
    missing_args

  let spill_term state loc modes types argmap term =

    let argmap = ref argmap in
    let state = ref state in

    let mk_Arg n =
      let s, m, (x,_) = raw_mk_Arg !state n !argmap in
      argmap := m;
      state := s;
      x in

    let allocate_bound_symbol n =
      let s, x = Symbols.allocate_bound_symbol !state n in
      state := s;
      x in

    let mkAppC c = function
      | [] -> Symbols.get_canonical !state c
      | x::xs -> App(c,x,xs) in

    let mkApp hd args =
      match hd with
      | App(c,x,xs) -> App(c,x,xs @ args)
      | Const c -> mkAppC c args
      | Builtin(c,xs) -> Builtin(c,xs @ args)
      | _ -> assert false in

    let mkSpilled =
      let spilled = ref 0 in
      let rec aux_mks vars n =
        if n == 0 then []
        else begin
          incr spilled;
          mkApp (mk_Arg ("Spilled_" ^ string_of_int !spilled)) vars ::
            aux_mks vars (n-1)
        end in
      fun vars n -> List.rev (aux_mks vars n) in

    let mkAppSpilled fcall args =
      let rec on_last f = function
        | [] -> assert false
        | [x] -> [f x]
        | x::xs -> x :: on_last f xs
      in
      let rec aux_mka = function
        | App(c,x,[y]) when c == D.Global_symbols.implc ->
            mkAppC c [x;aux_mka y]
        | App (c,x,xs) when c == D.Global_symbols.andc ->
            mkAppC c (on_last aux_mka (x::xs))
        | t -> mkApp t args
      in
        aux_mka fcall in

    let equal_term c = function
      | Const d -> c == d
      | _ -> false in

    let rec drop n = function
      | [] -> []
      | _ :: xs when n > 0 -> drop (n-1) xs
      | x -> x in

    let size_outermost_spill ~default l =
      match List.rev l with
      | [] -> default
      | (size, _) :: _ -> List.length size in

    let rec apply_to names variable = function
      | Const f when List.exists (equal_term f) names ->
          mkAppC f [variable]
      | (Const _ | CData _ | Nil | Discard) as x -> x
      | Cons(hd,tl) ->
          Cons(apply_to names variable hd,apply_to names variable tl)
      | Lam t -> Lam (apply_to names variable t)
      | App(f,x,xs) when List.exists (equal_term f) names ->
          mkAppC f (List.map (apply_to names variable) (x::xs) @ [variable])
      | App(hd,x,xs) -> mkAppC hd (List.map (apply_to names variable) (x::xs))
      | Builtin(hd,xs) -> Builtin(hd, List.map (apply_to names variable) xs)
      | (Arg _ | AppArg _ | UVar _ | AppUVar _) -> assert false in

    let add_spilled sp t =
      if sp = [] then t else
      mkAppC D.Global_symbols.andc (List.map snd sp @ [t]) in

    let rec spaux (depth,vars as ctx) = function
      | App(c, fcall, rest) when c == D.Global_symbols.spillc ->
         if (rest <> []) then
           error ~loc "A spill expression cannot be applied to an argument";
         let spills, fcall = spaux1 ctx fcall in
         let args =
            mkSpilled (List.rev vars) (missing_args_of !state loc modes types fcall) in
         spills @ [args, mkAppSpilled fcall args], args
      | App(c, Lam arg, []) when c == D.Global_symbols.pic ->
         let ctx = depth+1, allocate_bound_symbol depth :: vars in
         let spills, arg = spaux1 ctx arg in
         [], [mkAppC c [Lam (add_spilled spills arg)]]
      | App(c, Lam arg, []) when c == D.Global_symbols.sigmac ->
         let ctx = depth+1, vars in
         let spills, arg = spaux1 ctx arg in
         [], [mkAppC c [Lam (add_spilled spills arg)]]
      | App(c, hyp, [concl]) when c == D.Global_symbols.implc ->
         let spills_hyp, hyp1 = spaux1 ctx hyp in
         let t = spaux1_prop ctx concl in
         if (spills_hyp != []) then
           error ~loc "Cannot spill in the head of a clause";
         [], [mkAppC c (hyp1 :: t)]
      | App(c, concl, [hyp]) when c == D.Global_symbols.rimplc ->
         let t = spaux1_prop ctx hyp in
         let spills_concl, concl1 = spaux1 ctx concl in
         if (spills_concl != []) then
           error ~loc "Cannot spill in the head of a clause";
         [], [mkAppC c (concl1 :: t)]
      | App(hd,x,xs) ->
         let args = x :: xs in
         let spills, args, is_prop =
           let (@@@) (s1,a1) (s2,a2,b) = s1 @ s2, a1 @ a2, b in
           let rec aux_spaux ty args = match ty, args with
             | (Variadic(_,Prop) | Arrow([],Prop)), [] -> [],[],true
             | _, [] -> [],[],false
             | Variadic(Prop,_), a1 :: an ->
                   ([],spaux1_prop ctx a1) @@@ aux_spaux ty an
             | Arrow(Prop :: ty,c), a1 :: an ->
                   ([],spaux1_prop ctx a1) @@@ aux_spaux (Arrow(ty,c)) an
             | Arrow((_ :: _ as ty),c), a1 :: an ->
                   let spills, a1 = spaux ctx a1 in
                   let ty = drop (size_outermost_spill spills ~default:1) ty in
                   (spills, a1) @@@ aux_spaux (Arrow(ty,c)) an
             | _, a1 :: an -> spaux ctx a1 @@@ aux_spaux ty an
           in
             aux_spaux (type_of_const !state types hd) args in
         if is_prop then [], [add_spilled spills (mkAppC hd args)]
         else spills, [mkAppC hd args]
      | (CData _ | Const _ | Discard | Nil) as x -> [],[x]
      | Cons(hd,tl) ->
         let sp1, hd = spaux ctx hd in
         let sp2, tl = spaux ctx tl in
         (* FIXME: it could be in prop *)
         assert(List.length hd = 1 && List.length tl = 1);
         sp1 @ sp2, [Cons(List.hd hd, List.hd tl)]
      | Builtin(c,args) ->
         let spills, args = map_acc (fun sp x ->
           let sp1, x = spaux ctx x in
           sp @ sp1, x) [] args in
         [], [add_spilled spills (Builtin(c,List.concat args))]
      | Lam t ->
         let sp, t = spaux1 (depth+1, allocate_bound_symbol depth :: vars) t in
         let (t,_), sp = map_acc (fun (t,n) (names, call) ->
               let all_names = names @ n in
               let call = apply_to all_names (allocate_bound_symbol depth) call in
               let t = apply_to names (allocate_bound_symbol depth) t in
               (t,all_names), (names, mkAppC D.Global_symbols.pic [Lam call])
           ) (t,[]) sp in
         sp, [Lam t]
      | (UVar _ | AppUVar _) -> error ~loc "Stack term contains UVar"
      | (Arg _ | AppArg _) -> assert false

    and spaux1 ctx t =
      let spills, ts = spaux ctx t in
      if (List.length ts != 1) then
        error ~loc ("Spilling: expecting only one term at: " ^ show_term t);
      spills, List.hd ts

    and spaux1_prop (_, _ as ctx) t =
      let spills, ts = spaux ctx t in
      if (List.length ts != 1) then
        error ~loc ("Spilling: expecting only one term at: " ^ show_term t);
      [add_spilled spills (List.hd ts)]

    in

    let sp, term = spaux (0,[]) term in
    assert(List.length term = 1);
    let term = List.hd term in
    if (sp != []) then
      error ~loc ("Spilling: could not place " ^ show_term (snd (List.hd sp)));
    !argmap, term

  let spill_presequent state modes types loc pamap ({ pconclusion } as s) =
    let pamap, pconclusion = spill_term state loc modes types pamap pconclusion in
    pamap, { s with pconclusion }

  let spill_rule state modes types ({ pguard; pnew_goal; pamap; pcloc } as r) =
    let pamap, pguard = option_mapacc (spill_term state pcloc modes types) pamap pguard in
    let pamap, pnew_goal =
      option_mapacc (spill_presequent state modes types pcloc) pamap pnew_goal in
    { r with pguard; pnew_goal; pamap }

  let spill_chr state ~types ~modes {ctx_filter; clique; rules} =
    let rules = List.map (spill_rule state modes types) rules in
    {ctx_filter; clique; rules}

  let spill_clause state ~types ~modes ({ Ast.Clause.body = { term; amap; loc; spilling } } as x) =
    if not spilling then x
    else
      let amap, term = spill_term state loc modes types amap term in
      { x with Ast.Clause.body = { term; amap; loc; spilling = false } }

  let spill_preterm state types modes ({ term; amap; loc; spilling } as x) =
    if not spilling then x
    else
      let amap, term = spill_term state loc modes types amap term in
      { amap; term; loc; spilling = false; }

end (* }}} *)
 *)


(* let stack_term_of_preterm ~depth:arg_lvl state { term = t; amap = { c2i } } =
  let state = ref state in
  let get_global_or_allocate_bound_symbol n =
    let s, t = Symbols.get_global_or_allocate_bound_symbol !state n in
    state := s;
    t in
  let rec stack_term_of_preterm = function
    | Const c when C.Map.mem c c2i ->
        let argno = C.Map.find c c2i in
        R.mkAppArg argno arg_lvl []
    | Const c -> get_global_or_allocate_bound_symbol c
    | App(c, x, xs) when C.Map.mem c c2i ->
        let argno = C.Map.find c c2i in
        R.mkAppArg argno arg_lvl (List.map stack_term_of_preterm (x::xs))
    | App(c, x, xs) as app ->
        let x1 = stack_term_of_preterm x in
        let xs1 = smart_map stack_term_of_preterm xs in
        if x1 == x && xs1 == xs then app else App(c, x1, xs1)
    | Lam t as x ->
        let t1 = stack_term_of_preterm  t in
        if t1 == t then x else Lam t1
    | CData _ as x -> x
    | Builtin(c, args) as x ->
        let args1 = smart_map stack_term_of_preterm args in
        if args1 == args then x else Builtin(c, args1)
    | UVar _ | AppUVar _ | Arg _ | AppArg _ -> anomaly "preterm containing a variable"
    | Nil as x -> x
    | Discard as x -> x
    | Cons(hd, tl) as x ->
        let hd1 = stack_term_of_preterm hd in
        let tl1 = stack_term_of_preterm tl in
        if hd == hd1 && tl == tl1 then x else Cons(hd1,tl1)
  in
  let t = stack_term_of_preterm t in
  !state, t *)
;;

(* This is marshalable *)

module Assemble : sig

  val extend : flags -> State.t -> Assembled.program -> compilation_unit list -> State.t * Assembled.program

  (* for the query *)
  val compile_query : State.t -> Assembled.program -> ScopedTerm.t -> SymbolMap.table * int F.Map.t * D.term

end = struct

  let chose_indexing state predicate l k =
    let all_zero = List.for_all ((=) 0) in
    let rec check_map default argno = function
      (* TODO: @FissoreD here we should raise an error if n > arity of the predicate? *)
      | [] -> error ("Wrong indexing for " ^ F.show predicate ^ ": no argument selected.")
      | 0 :: l -> check_map default (argno+1) l
      | 1 :: l when all_zero l -> MapOn argno
      | _ -> default ()
    in
    match k with
    | Some Ast.Structured.DiscriminationTree -> DiscriminationTree l
    | Some HashMap -> Hash l
    | None -> check_map (fun () -> DiscriminationTree l) 0 l
    | Some Map -> check_map (fun () ->
        error ("Wrong indexing for " ^ F.show predicate ^
                ": Map indexes exactly one argument at depth 1")) 0 l

  let update_indexing state symbols ({ idx } as index) modes types old_idx =
    let check_if_some_clauses_already_in ~loc predicate c =
         if Ptmap.mem c idx then
           error ~loc @@ "Some clauses for " ^ F.show predicate ^
             " are already in the program, changing the indexing a posteriori is not allowed."
      in
    let add_indexing_for ~loc name c tindex map =
      let mode = try fst @@ F.Map.find name modes with Not_found -> [] in
      let declare_index, index =
        match tindex with
        | Some (Ast.Structured.Index(l,k)) -> true, chose_indexing state name l k
        | _ -> false, chose_indexing state name [1] None in
      try
        let _, old_tindex =
          try C.Map.find c map
          with Not_found -> C.Map.find c old_idx in
        if old_tindex <> index then
          if old_tindex <> MapOn 1 && declare_index then
            error ~loc ("multiple and inconsistent indexing attributes for " ^
                      F.show name)
          else
            if declare_index then begin
              check_if_some_clauses_already_in ~loc name c;
               C.Map.add c (mode,index) map
            end else map
        else
          map
      with Not_found ->
        check_if_some_clauses_already_in ~loc name c;
        C.Map.add c (mode,index) map in

    let symbols, map =
      F.Map.fold (fun tname l (symbols, acc) ->
        let symbols, (c,_) = SymbolMap.allocate_global_symbol state symbols tname in
        symbols, TypeList.fold (fun acc { ScopedTypeExpression.indexing; loc } ->
                   add_indexing_for ~loc tname c indexing acc)
                  acc l)
      types (symbols, C.Map.empty) in
    let symbols, map =
      F.Map.fold (fun k (_,loc) (symbols,m) ->
        let symbols, (c,_) = SymbolMap.allocate_global_symbol state symbols k in
        symbols, add_indexing_for ~loc k c None m) modes (symbols, map) in
    symbols, R.CompileTime.update_indexing map index, C.Map.union (fun _ _ _ -> assert false) map old_idx

  let todbl state symb ?(amap = F.Map.empty) t =
    let symb = ref symb in
    let amap = ref amap in
    let allocate_arg c =
      try F.Map.find c !amap
      with Not_found ->
        let n = F.Map.cardinal !amap in
        amap := F.Map.add c n !amap;
        n in
    let allocate_global_symbol c =
      let s, rc = SymbolMap.allocate_global_symbol state !symb c in
      symb := s;
      rc in
    let lookup_bound loc (_,ctx) c =
      try F.Map.find c ctx
      with Not_found -> error ~loc ("Unbound variable " ^ F.show c) in
    let allocate_bound_symbol loc ctx f =
      let c = lookup_bound loc ctx f in
      let s, rc = SymbolMap.allocate_bound_symbol state !symb f c in
      symb := s;
      rc in
    let push_bound (n,ctx) c = (n+1,F.Map.add c n ctx) in
    let push_unnamed_bound (n,ctx) = (n+1,ctx) in
    let open ScopedTerm in
    let rec todbl ctx t =
      match t.it with
      | CData c -> D.mkCData (CData.hcons c)
      | Spill(t,n) -> assert(n=0); assert false
      (* lists *)
      | Const(Global,c) when F.(equal c nilf) -> D.mkNil
      | App(Global,c,x,[y]) when F.(equal c consf) ->
          let x = todbl ctx x in
          let y = todbl ctx y in
          D.mkCons x y
      (* globals and builtins *)
      | Const(Global,c) ->
          let c, t = allocate_global_symbol c in
          if Builtins.is_declared state c then D.mkBuiltin c []
          else t
      | App(Global,c,x,xs) ->
          let c,_ = allocate_global_symbol c in
          let x = todbl ctx x in
          let xs = List.map (todbl ctx) xs in
          if Builtins.is_declared state c then D.mkBuiltin c (x::xs)
          else D.mkApp c x xs
      (* lambda terms *)
      | Const(Local,c) -> allocate_bound_symbol t.loc ctx c
      | Lam(None,t) -> D.mkLam @@ todbl (push_unnamed_bound ctx) t
      | Lam(Some c,t) -> D.mkLam @@ todbl (push_bound ctx c) t
      | App(Local,c,x,xs) ->
          let c = lookup_bound t.loc ctx c in
          let x = todbl ctx x in
          let xs = List.map (todbl ctx) xs in
          D.mkApp c x xs
      (* holes *)
      | Var(c,xs) ->
          let xs = List.map (todbl ctx) xs in
          R.mkAppArg (allocate_arg c) 0 xs
      | Discard -> D.mkDiscard
    in
    let t  = todbl (0,F.Map.empty) t in
    (!symb, !amap), t  

  let extend1_clause flags state modes indexing (symbols, index) { Ast.Clause.body; loc; attributes = { Ast.Structured.insertion = graft; id; ifexpr } } =
    if not @@ filter1_if flags (fun x -> x) ifexpr then
      (symbols, index)
    else
    let (symbols, amap), body = todbl state symbols body in
    let modes x = try fst @@ F.Map.find (SymbolMap.global_name state symbols x) modes with Not_found -> [] in
    let (p,cl), _, morelcs =
      try R.CompileTime.clausify1 ~loc ~modes ~nargs:(F.Map.cardinal amap) ~depth:0 body
      with D.CannotDeclareClauseForBuiltin(loc,c) ->
        error ?loc ("Declaring a clause for built in predicate " ^ F.show @@ SymbolMap.global_name state symbols c)
      in
    if morelcs <> 0 then error ~loc "sigma in a toplevel clause is not supported";
    let index = R.CompileTime.add_to_index ~depth:0 ~predicate:p ~graft cl id index in
    symbols, index


  let check_rule_pattern_in_clique state symbols clique { D.CHR.pattern; rule_name; rule_loc } =
    try
      let outside =
        List.find (fun x -> not (D.CHR.in_clique clique x)) pattern in
      error ~loc:rule_loc ("CHR rule " ^ rule_name ^ ": matches " ^ (F.show @@ SymbolMap.global_name state symbols outside) ^
        " which is not a constraint on which it is applied. Check the list of predicates after the \"constraint\" keyword.");
    with Not_found -> ()
    
  let extend1_chr flags state clique (symbols,chr) { Ast.Chr.to_match; to_remove; guard; new_goal; attributes; loc } =
    if not @@ filter1_if flags (fun x -> x.Ast.Structured.cifexpr) attributes then
      (symbols,chr)
    else
    let todbl state (symbols,amap) t = todbl state symbols ~amap t in
    let sequent_todbl state st { Ast.Chr.eigen; context; conclusion } =
      let st, eigen = todbl state st eigen in
      let st, context = todbl state st context in
      let st, conclusion = todbl state st conclusion in
      st, { CHR.eigen; context; conclusion } in
    let st = symbols, F.Map.empty in
    let st, to_match = map_acc (sequent_todbl state) st to_match in
    let st, to_remove = map_acc (sequent_todbl state) st to_remove in
    let st, guard = option_mapacc (todbl state) st guard in
    let st, new_goal = option_mapacc (sequent_todbl state) st new_goal in
    let symbols, amap = st in

    let key_of_sequent { CHR.conclusion } =
      match conclusion with
      | Const x -> x
      | App(x,_,_) -> x
      | _ -> error ~loc "CHR: rule without head symbol" in
    let all_sequents = to_match @ to_remove in
    let pattern = List.map key_of_sequent all_sequents in
    let rule_name = attributes.Ast.Structured.cid in
  
    let patsno = List.(length to_match + length to_remove) in
    let nargs = F.Map.cardinal amap in
    let rule = { CHR.to_match; nargs; to_remove; guard; new_goal; patsno; pattern; rule_name; rule_loc = loc  } in
    check_rule_pattern_in_clique state symbols clique rule;
    symbols, CHR.add_rule clique rule chr

  let extend1_chr_block flags state (symbols,chr) { Ast.Structured.clique; ctx_filter; rules } =
    let allocate_global_symbol state symbols f =
      let symbols, (c,_) = SymbolMap.allocate_global_symbol state symbols f in
      symbols, c in
    let symbols, clique = map_acc (allocate_global_symbol state) symbols clique in
    let symbols, ctx_filter = map_acc (allocate_global_symbol state) symbols ctx_filter in
    let chr, clique = CHR.new_clique (SymbolMap.global_name state symbols) ctx_filter clique chr in
    List.fold_left (extend1_chr flags state clique) (symbols,chr) rules
   
  let merge_type_abbrevs m1 m2 =
    F.Map.union (fun k _ _ -> error ("Duplicate type abbreviation for " ^ F.show k)) m1 m2

  let extend1 flags
    (state, { Assembled.symbols; prolog_program; indexing; modes = om; kinds = ok; types = ot; type_abbrevs = ota; chr = ochr; toplevel_macros = otlm; total_type_checking_time })
            { version; code = { Flat.toplevel_macros; kinds; types; type_abbrevs; modes; clauses; chr; builtins }} =
    let symbols, prolog_program, indexing = update_indexing state symbols prolog_program modes types indexing in
    let kinds = Flatten.merge_kinds ok kinds in
    let modes = Flatten.merge_modes om modes in

    let type_abbrevs =
      List.fold_left (fun type_abbrevs (name, ty) ->
        (* TODO check dijoint from kinds and type_abbrevs *)
        F.Map.add name (TypeChecker.check_type ~type_abbrevs kinds ty) type_abbrevs)
        ota type_abbrevs in


    let type_abbrevs = merge_type_abbrevs ota type_abbrevs in

    let t0 = Unix.gettimeofday () in
    (* TypeChecker.check_disjoint ~type_abbrevs ~kinds; *)
    let types = F.Map.map (TypeChecker.check_types ~type_abbrevs kinds) types in
    let t1 = Unix.gettimeofday () in
    let total_type_checking_time = total_type_checking_time +. t1 -. t0 in

    let types = Flatten.merge_type_assignments ot types in


    let symbols, state =
      List.fold_left (fun (symbols,state) (D.BuiltInPredicate.Pred(name,_,_) as p) ->
        let symbols, (c,_) = SymbolMap.allocate_global_symbol state symbols (F.from_string name) in
        let state = Builtins.register state p c in
        symbols,state) (symbols,state) builtins in

    (* TODO: make this callable on a unit (+ its base) *)
    let t0 = Unix.gettimeofday () in
    clauses |> List.iter (fun { Ast.Clause.body; loc; attributes = { Ast.Structured.typecheck } } ->
      if typecheck then
        ignore @@ TypeChecker.check ~type_abbrevs ~kinds ~env:types body ~exp:TypeAssignment.(Val Prop)
    );
    let t1 = Unix.gettimeofday () in
    let total_type_checking_time = total_type_checking_time +. t1 -. t0 in


    let symbols, chr =
      List.fold_left (extend1_chr_block flags state) (symbols,ochr) chr in
    let symbols, prolog_program =
      List.fold_left (extend1_clause flags state modes indexing) (symbols, prolog_program) clauses in

    state, { Assembled.symbols; prolog_program; indexing; modes; kinds; types; type_abbrevs; chr; toplevel_macros; total_type_checking_time }

  let extend flags state assembled ul =
    List.fold_left (extend1 flags) (state, assembled) ul

  let compile_query state { Assembled.symbols; } t =
    let (symbols, amap), t = todbl state symbols t in
    symbols, amap, t 

end


(****************************************************************************
  API
 ****************************************************************************)

(* let rec constants_of acc = function
  | D.Const x -> C.Set.add x acc
  | D.App(c,x,xs) -> List.fold_left constants_of (constants_of (C.Set.add c acc) x) xs
  | D.Cons(x,xs) -> constants_of (constants_of acc x) xs
  | D.Lam x -> constants_of acc x
  | D.Builtin(c,xs) -> List.fold_left constants_of (C.Set.add c acc) xs
  | D.AppArg _ | D.Arg _
  | D.AppUVar _ | D.UVar _ -> anomaly "relocate_closed_term: not a closed term"
  | D.Nil | D.Discard | D.CData _ -> acc

  let relocate_closed_term ~from =
    let table = State.get Symbols.table from in
    fun ~to_ t ->
      let alive = constants_of C.Set.empty t in
      let table = Symbols.prune table ~alive in
      let base = State.update Symbols.table to_ Symbols.lock in
      Stdlib.Result.bind (Symbols.build_shift ~lock_base:true ~flags:default_flags ~base table)
        (fun (base, shift) -> Stdlib.Result.Ok (Flatten.relocate_term to_ shift t))

let w_symbol_table s f x =
  let table = Symbols.compile_table @@ State.get Symbols.table s in
  let pp_ctx = { table; uv_names = ref (IntMap.empty,0) } in
  Util.set_spaghetti_printer pp_const (R.Pp.pp_constant ~pp_ctx);
  f x *)

(* Compiler passes *)
let unit_or_header_of_ast { print_passes } s ?(toplevel_macros=F.Map.empty) p =

  if print_passes then
    Format.eprintf "== AST ================@\n@[<v 0>%a@]@\n"
      Ast.Program.pp p;

  let p = RecoverStructure.run s p in

  if print_passes then
    Format.eprintf "== Ast.Structured ================@\n@[<v 0>%a@]@\n"
      Ast.Structured.pp_program p;

  let s, p = Scope_Quotation_Macro.run s p in

  if print_passes then
    Format.eprintf "== Scoped ================@\n@[<v 0>%a@]@\n"
      Scoped.pp_program p;

  let p = Flatten.run s p in

  if print_passes then
    Format.eprintf "== Flat ================@\n@[<v 0>%a@]@\n"
      Flat.pp_program p;

  s, {
    version = "%%VERSION_NUM%%";
    code = p;
  }, toplevel_macros
;;

let print_unit { print_units } x =
    if print_units then
      let b1 = Marshal.to_bytes x.code [] in
      Printf.eprintf "== UNIT =================\ncode: %dk (%d clauses)\n\n%!"
        (Bytes.length b1 / 1024) (List.length x.code.Flat.clauses)
;;

let header_of_ast ~flags ~parser:p state_descriptor quotation_descriptor hoas_descriptor calc_descriptor builtins ast : header =
  let state = D.State.(init (merge_descriptors D.elpi_state_descriptor state_descriptor)) in
  let state =
    match hoas_descriptor.D.HoasHooks.extra_goals_postprocessing with
    | Some x ->
        D.State.set D.Conversion.extra_goals_postprocessing state x
    | None -> state in
  let { D.QuotationHooks.default_quotation;
        named_quotations;
        singlequote_compilation;
        backtick_compilation } = quotation_descriptor in

  let state = D.State.set CustomFunctorCompilation.backtick state (Option.map snd backtick_compilation) in
  let state = D.State.set CustomFunctorCompilation.singlequote state (Option.map snd singlequote_compilation) in
  let state = D.State.set Quotation.default_quotation state default_quotation in
  let state = D.State.set Quotation.named_quotations state named_quotations in
  let state =
    let eval_map = List.fold_left (fun m (c,{ CalcHooks.code }) -> Constants.Map.add c code m) Constants.Map.empty (List.rev calc_descriptor) in
    D.State.set CalcHooks.eval state eval_map in
  let state = D.State.set parser state (Some p) in
  let state = D.State.set D.while_compiling state true in
  (* let state = State.set Symbols.table state (Symbols.global_table ()) in *)
  let state, u, toplevel_macros = unit_or_header_of_ast flags state ast in
  let builtins =
    List.flatten @@
    List.map (fun (_,decl) -> decl |> List.filter_map (function
      | Data.BuiltInPredicate.MLCode (p,_) -> Some p
      | _ -> None)) builtins in
  let u = { u with code = { u.code with builtins }} in (* UGLY *)
  print_unit flags u;
  state, u, toplevel_macros

let unit_of_ast ~flags ~header:(s, (header : compilation_unit), toplevel_macros) p : compilation_unit =
  let _, u, _ = unit_or_header_of_ast flags s ~toplevel_macros p in
  print_unit flags u;
  u

let assemble_units ~flags ~header:(s,h,toplevel_macros) units : program =

  let init = { (Assembled.empty ()) with toplevel_macros } in

  let s, p = Assemble.extend flags s init (h :: units) in

  let { print_passes } = flags in

  if print_passes then
    Format.eprintf "== Assembled ================@\n@[<v 0>%a@]@\n"
      Assembled.pp_program p;

 s, p
;;

let append_units ~flags ~base:(s,p) units : program =
  let s, p = Assemble.extend flags s p units in
  let { print_passes } = flags in

  if print_passes then
    Format.eprintf "== Assembled ================@\n@[<v 0>%a@]@\n"
     Assembled.pp_program p;

  s, p

let program_of_ast ~flags ~header p : program =
  let u = unit_of_ast ~flags ~header p in
  assemble_units ~flags ~header [u]

let is_builtin state tname =
  Builtins.is_declared state tname

let check_all_builtin_are_typed state types = () (*
   C.Set.iter (fun c ->
     if not (match C.Map.find c types with
     | l -> l |> Types.for_all (fun { Types.tindex;_} -> tindex = Ast.Structured.External)
     | exception Not_found -> false) then
       error ("Built-in without external type declaration: " ^ Symbols.show state c))
   (Builtins.all state);
  F.Map.iter (fun tname tl -> tl |> Types.iter (fun { Types.tindex; decl = { tname; tloc }} ->
    if tindex = Ast.Structured.External && not (is_builtin state tname) then
      error ~loc:tloc ("external type declaration without Built-in: " ^
            Symbols.show state tname)))
  types
;;
*)

let check_no_regular_types_for_builtins state types = () (*
  C.Map.iter (fun tname l -> l |> Types.iter (fun {Types.tindex; decl = { tloc } } ->
    if tindex <> Ast.Structured.External && is_builtin state tname then
      anomaly ~loc:tloc ("type declaration for Built-in " ^
            Symbols.show state tname ^ " must be flagged as external");
 )) types
*)

let uvbodies_of_assignments assignments =
  (* Clients may add spurious args that, not occurring in the query,
     are not turned into uvars *)
   let assignments = assignments |> StrMap.filter (fun _ -> function
     | UVar _ | AppUVar _ -> true
     | _ -> false) in
   State.end_goal_compilation (StrMap.map (function
     | UVar(b,_,_) | AppUVar(b,_,_) -> b
     | _ -> assert false) assignments)

let query_of_ast (compiler_state, assembled_program) t state_update =
  let compiler_state = State.begin_goal_compilation compiler_state in
  let types = assembled_program.Assembled.types in
  let type_abbrevs = assembled_program.Assembled.type_abbrevs in
  let modes = assembled_program.Assembled.modes in
  let kinds = assembled_program.Assembled.kinds in

  let active_macros = assembled_program.Assembled.toplevel_macros in
  let total_type_checking_time = assembled_program.Assembled.total_type_checking_time in

  let t = Scope_Quotation_Macro.scope_loc_term t in
  (* TODOtypecheck query *)
  let symbols, amap, query = Assemble.compile_query compiler_state assembled_program t in
  let query_env = Array.make (F.Map.cardinal amap) D.dummy in
  let initial_goal = R.move ~argsdepth:0 ~from:0 ~to_:0 query_env query in
  let assignments = F.Map.fold (fun k i m -> StrMap.add (F.show k) query_env.(i) m) amap StrMap.empty in
  {
    WithMain.types;
    kinds;
    modes;
    type_abbrevs;
    prolog_program = assembled_program.Assembled.prolog_program;
    (* clauses = assembled_program.Assembled.clauses; *)
    chr = assembled_program.Assembled.chr;
    (* initial_depth; *)
    (* query; *)
    symbols;
    query_arguments = Query.N;
    initial_goal;
    assignments;
    compiler_state = compiler_state |> (uvbodies_of_assignments assignments) |> state_update;
    total_type_checking_time;
  }

let total_type_checking_time { WithMain.total_type_checking_time = x } = x

let query_of_term (compiler_state, assembled_program) f = assert false (*
  let compiler_state = State.begin_goal_compilation compiler_state in
  let initial_depth = assembled_program.Assembled.local_names in
  let types = assembled_program.Assembled.types in
  let type_abbrevs = assembled_program.Assembled.type_abbrevs in
  let modes = C.Map.map fst assembled_program.Assembled.modes in
  let active_macros = assembled_program.Assembled.toplevel_macros in
  let state, query =
    ToDBL.query_preterm_of_function
      ~depth:initial_depth active_macros compiler_state
      (f ~depth:initial_depth) in
  let query_env = Array.make query.amap.nargs D.dummy in
    let state, queryt = stack_term_of_preterm ~depth:initial_depth state query in
  let initial_goal =
    R.move ~argsdepth:initial_depth ~from:initial_depth ~to_:initial_depth query_env
      queryt in
  let assignments = StrMap.map (fun i -> query_env.(i)) query.amap.n2i in
 {
    WithMain.types;
    type_abbrevs;
    modes;
    clauses = assembled_program.clauses;
    prolog_program = assembled_program.prolog_program;
    chr = assembled_program.Assembled.chr;
    initial_depth;
    query;
    query_arguments = Query.N;
    initial_goal;
    assignments;
    compiler_state = state |> (uvbodies_of_assignments assignments);
  }

*)

let query_of_data (state, p) loc (Query.Query { arguments } as descr) = assert false (*
  let query = query_of_term (state, p) (fun ~depth state ->
    let state, term, gls = R.embed_query ~mk_Arg ~depth state descr in
    state, (loc, term), gls) in
  { query with query_arguments = arguments }
*)

(* let lookup_query_predicate (state, p) pred =
  let state, pred = Symbols.allocate_global_symbol_str state pred in
  (state, p), pred *)

module Compiler : sig

  (* Translates preterms in terms and AST clauses into clauses (with a key,
   * subgoals, etc *)

  val run : 'a query -> 'a executable

end = struct (* {{{ *)


let run
  {
    WithMain.types;
    modes;
    (* clauses = _; *)
    prolog_program;
    chr;
    (* initial_depth; *)
    symbols;
    initial_goal;
    assignments;
    compiler_state = state;
    query_arguments;
  }
=
  check_all_builtin_are_typed state types;
  check_no_regular_types_for_builtins state types;
  (* Real Arg nodes: from "Const '%Arg3'" to "Arg 3" *)
  (* let compiler_symbol_table = State.get Symbols.table state in *)
  let builtins = Hashtbl.create 17 in
  let pred_list = (State.get Builtins.builtins state).code in
  let _ = List.fold_left
    (fun symbols (D.BuiltInPredicate.Pred(s,_,_) as p) ->
      let symbols, (c, _) = SymbolMap.allocate_global_symbol state symbols (F.from_string s) in (* TODO: preallocate all builtins, new API to assert *)
      Hashtbl.add builtins c p;
      symbols) symbols
    pred_list in
  let symbol_table = SymbolMap.compile symbols in
  {
    D.compiled_program = { index = close_index prolog_program; src = [] };
    chr;
    initial_depth = 0;
    initial_goal;
    initial_runtime_state = State.end_compilation state;
    assignments;
    query_arguments;
    symbol_table;
    builtins;
  }

end (* }}} *)

let optimize_query = Compiler.run

let removals l =
  l |> List.filter_map (fun c -> match c.Ast.Clause.attributes.Assembled.insertion with Some (Remove x) -> Some x | Some (Replace x) -> Some x| _ -> None)

let handle_clause_graftin clauses =
  let clauses = clauses |> List.sort (fun c1 c2 -> R.lex_insertion c1.Ast.Clause.attributes.Assembled.timestamp c2.Ast.Clause.attributes.Assembled.timestamp) in
  let removals = removals clauses in
  let clauses = clauses |> List.filter (fun c -> let id = c.Ast.Clause.attributes.Assembled.id in id = None || not(List.exists (fun x -> id = Some x) removals)) in
  let clauses = clauses |> List.filter (fun c -> match c.Ast.Clause.attributes.Assembled.insertion with Some (Remove _) -> false | _ -> true) in
  clauses

let pp_program pp fmt _ = assert false (*{
    (* WithMain.clauses; *)
    (* initial_depth; *)
    compiler_state; } =

  let clauses = handle_clause_graftin clauses in

  let compiler_state, clauses =
    map_acc (fun state { Ast.Clause.body; loc; attributes = { Assembled.id; timestamp } } ->
       let state, c = stack_term_of_preterm ~depth:initial_depth state body in
       state, (c,loc,id,timestamp))
    compiler_state clauses in
  let pp_ctx = {
    uv_names = ref (IntMap.empty, 0);
    table = Symbols.compile_table (State.get Symbols.table compiler_state);
  } in
  Format.fprintf fmt "@[<v>";
  List.iter (fun (body,loc,name,timestamp) ->
    Format.fprintf fmt "@[<h>%% [%a] %a %a@]@;" Format.(pp_print_list ~pp_sep:(fun fmt () -> pp_print_string fmt "; ") pp_print_int) timestamp Loc.pp loc Format.(pp_print_option (fun fmt x -> pp_print_string fmt x)) name ;
    Format.fprintf fmt "%a.@;" (pp ~pp_ctx ~depth:initial_depth) body)
    clauses;
  Format.fprintf fmt "@]"
;;*)
let pp_goal pp fmt _ = assert false (* {
    WithMain.initial_depth;
    compiler_state;
    query; } =
  let compiler_state, goal = stack_term_of_preterm compiler_state ~depth:initial_depth query in
  let pp_ctx = {
    uv_names = ref (IntMap.empty, 0);
    table = Symbols.compile_table (State.get Symbols.table compiler_state);
  } in
  Format.fprintf fmt "@[<v>";
  Format.fprintf fmt "%a.@;" (pp ~pp_ctx ~depth:initial_depth) goal;
  Format.fprintf fmt "@]"
;;
*)

(****************************************************************************
  Quotation (for static checkers, see elpi-quoted_syntax.elpi)
 ****************************************************************************)

let constc   = D.Global_symbols.declare_global_symbol "const"
let tconstc  = D.Global_symbols.declare_global_symbol "tconst"
let appc     = D.Global_symbols.declare_global_symbol "app"
let tappc    = D.Global_symbols.declare_global_symbol "tapp"
let lamc     = D.Global_symbols.declare_global_symbol "lam"
let cdatac   = D.Global_symbols.declare_global_symbol "cdata"
let forallc  = D.Global_symbols.declare_global_symbol "forall"
let arrowc   = D.Global_symbols.declare_global_symbol "arrow"
let argc     = D.Global_symbols.declare_global_symbol "arg"
let discardc = D.Global_symbols.declare_global_symbol "discard"
let clausec  = D.Global_symbols.declare_global_symbol "clause"
let checkc   = D.Global_symbols.declare_global_symbol "check"
let colonc   = D.Global_symbols.declare_global_symbol "`:"
let colonec  = D.Global_symbols.declare_global_symbol "`:="
let truec    = D.Global_symbols.declare_global_symbol "true"
let falsec   = D.Global_symbols.declare_global_symbol "false"
let pairc    = D.Global_symbols.declare_global_symbol "pr"

let modefoc  = D.Global_symbols.declare_global_symbol "mode-fo"
let modehoc  = D.Global_symbols.declare_global_symbol "mode-ho"

let mkQApp ~on_type l =
  let c = if on_type then tappc else appc in
  App(c,R.list_to_lp_list l,[])
(* 
let mkQCon time ~compiler_state new_state ~on_type ?(amap=empty_amap) c =
  let allocate_bound_symbol =
    match time with
    | `Compiletime -> Symbols.allocate_bound_symbol
    | `Runtime f -> (fun s c -> s, f c) in
  try allocate_bound_symbol new_state (C.Map.find c amap.c2i)
  with Not_found ->
    let a = if on_type then tconstc else constc in
    if c < 0 then new_state, App(a,D.C.of_string (Symbols.show compiler_state c),[])
    else allocate_bound_symbol new_state (c + amap.nargs)

let quote_preterm time ~compiler_state new_state { term; amap } =
  let new_state = ref new_state in
  let mkQApp = mkQApp ~on_type:false in
  let mkQCon c =
    let n, x = mkQCon time ~compiler_state !new_state ~on_type:false ~amap c in
    new_state := n;
    x in
  let rec aux_quote depth term = match term with
    | Const n -> mkQCon n
    | Builtin(c,[]) -> mkQCon c
    | Lam x -> App(lamc,Lam (aux_quote (depth+1) x),[])
    | App(c,x,xs) ->
        mkQApp (mkQCon c :: List.(map (aux_quote depth) (x :: xs)))
    | Builtin(c,args) -> mkQApp (mkQCon c :: List.map (aux_quote depth) args)

(*
    | Arg(id,0) -> D.mkConst id
    | Arg(id,argno) -> mkQApp (D.mkConst id :: C.mkinterval vars argno 0)
    | AppArg(id,xs) -> mkQApp (D.mkConst id :: List.map (aux depth) xs)
*)
    | Arg _ | AppArg _ -> assert false

(*
    | UVar ({ contents = g }, from, args) when g != D.dummy ->
       aux depth (deref_uv ~from ~to_:depth args g)
    | AppUVar ({contents = t}, from, args) when t != D.dummy ->
       aux depth (deref_appuv ~from ~to_:depth args t)
*)
    | UVar _ | AppUVar _ -> assert false

    | CData _ as x -> App(cdatac,x,[])
    | Cons(hd,tl) -> mkQApp [mkQCon D.Global_symbols.consc; aux_quote depth hd; aux_quote depth tl]
    | Nil -> mkQCon D.Global_symbols.nilc
    | Discard -> mkQCon discardc
  in
  let term = aux_quote amap.nargs term in
  !new_state, term

let quote_pretype time ~compiler_state new_state { tloc; ttype; tamap } =
  let new_state = ref new_state in
  let mkQApp = mkQApp ~on_type:true in
  let mkQCon c =
    let n, x = mkQCon time ~compiler_state !new_state ~on_type:true ~amap:tamap c in
    new_state := n;
    x in
  let rec aux depth term : term = match term with
    | TApp(c,TCData s,[]) when c == D.Global_symbols.ctypec && D.C.is_string s -> App(c, CData s, [])
    | TArr (s, t) -> App(arrowc,aux depth s,[aux depth t])
    | TConst n when D.Global_symbols.propc = n -> Const n
    | TConst n -> mkQCon n
    | TLam x -> App(lamc,Lam (aux (depth+1) x),[])
    | TApp(c,x,xs) -> mkQApp (mkQCon c :: List.(map (aux depth) (x :: xs)))
    | TCData x -> App(cdatac, CData x,[])
    | TPred (f, l) -> 
        (* TODO: @FissoreD (flemma) for compatibility modes are ignored. Consider them! *)
        let l = List.rev_map snd l in
        let t = List.fold_left (fun acc e -> TArr (e, acc)) (TConst D.Global_symbols.propc) l in
        aux depth t
  in
  let term = aux tamap.nargs ttype in
  !new_state, term

(* FIXME : close_with_pis already exists but unused *)
let close_w_binder binder t { nargs } =
  let rec close = function
    | 0 -> t
    | n -> App(binder,Lam (close (n-1)),[]) in
  close nargs

let sorted_names_of_argmap argmap =
    IntMap.bindings argmap.i2n |>
    List.map snd |>
    List.map D.C.of_string

let quote_loc ?id loc =
  let source_name =
    match id with
    | Some x -> loc.Loc.source_name ^ ": " ^ x
    | None -> loc.Loc.source_name in
  Ast.cloc.CData.cin { loc with Loc.source_name }

let quote_clause time ~compiler_state new_state { Ast.Clause.loc; attributes = { Assembled.id }; body } =
  let clloc = quote_loc ?id loc in
  let new_state, bodyt = quote_preterm time ~compiler_state new_state body in
  let qt = close_w_binder argc bodyt body.amap in
  let names = sorted_names_of_argmap body.amap in
  new_state, App(clausec,CData clloc,[R.list_to_lp_list names; qt])
;;

let rec lam2forall = function
  | App(c,x,[]) when c == lamc -> mkApp forallc (lam2forall x) []
  | App(c,x,xs) -> mkApp c (lam2forall x) (List.map lam2forall xs)
  | (Const _ | Nil | CData _| Discard) as x -> x
  | Cons(x,xs) -> mkCons (lam2forall x) (lam2forall xs)
  | Builtin(c,xs) -> mkBuiltin c (List.map lam2forall xs)
  | Lam x -> mkLam (lam2forall x)
  | UVar _ | AppUVar _ -> assert false
  | Arg _ | AppArg _ -> assert false

let quote_syntax time new_state { WithMain.clauses; query; compiler_state } =
  let names = sorted_names_of_argmap query.amap in
  let clauses = handle_clause_graftin clauses in
  let new_state, clist = map_acc (quote_clause time ~compiler_state) new_state clauses in
  let new_state, queryt = quote_preterm time ~compiler_state new_state query in
  let q =
    App(clausec,CData (quote_loc ~id:"query" query.loc),
      [R.list_to_lp_list names;
       close_w_binder argc queryt query.amap]) in
  new_state, clist, q

let unfold_type_abbrevs ~is_typeabbrev ~compiler_state lcs type_abbrevs { ttype; tloc; tamap } ttime =
  let loc = tloc in
  let rec subst lvl (args: ttype array) = function
    | TConst c when c >= 0 -> args.(c)
    | TConst _ | TCData _ as t -> t
    | TLam t -> error ~loc "lambdas should be fully applied"
    | TArr (a, b) -> TArr (subst lvl args a, subst lvl args b)
    | TPred (f, l) -> TPred (f, List.map (fun (a,b) -> a, subst lvl args b) l)
    | TApp (a, b, c) -> TApp (a, subst lvl args b, List.map (subst lvl args) c)
  in
  let beta t args =
    let rec aux lvl t xs = 
    match t, xs with
    | TLam t', x::xs -> aux (lvl+1) t' xs
    | t, [] -> 
      subst 0 (Array.of_list args) t
    | _, _::_ -> error ~loc "higher-order types do not exist" in
    aux 0 t args
  in
  let error_undefined ~t1 ~t2 c (tavalue: pretype) =
    if is_typeabbrev && t1 <= t2 then
      error (Format.asprintf "typeabbrev %a uses the undefined %s constant at %a" pp_ttype tavalue.ttype (Symbols.show compiler_state c) Util.Loc.pp tavalue.tloc);
  in
  let find_opt c = C.Map.find_opt c type_abbrevs in
  (* DEBUG HELPER: Prints the type_abrev dictionary sorted by timestamp *)
  (* let _ =
    let x = C.Map.bindings type_abbrevs in
    let y = List.sort (fun (_, (x: type_abbrev_declaration)) (_, y) -> x.timestamp - y.timestamp) x in
    print_endline "---------------------------------------------";
    List.iter (fun (k,(v:type_abbrev_declaration)) ->
      Format.printf "TIME AND KEY %s -- %d\n%!" (Symbols.show compiler_state k) (v.timestamp)) y;
  in *)
  let rec aux_tabbrv ttime = function
    | Const c as x ->
        begin match find_opt c with
        | Some { tavalue; taparams; timestamp=time } ->
          if taparams > 0 then
            error ~loc ("type abbreviation " ^ Symbols.show compiler_state c ^ " needs " ^
              string_of_int taparams ^ " arguments");
          error_undefined ttime time c tavalue;
          aux time tavalue.ttype
        | None -> x
        end
    | TApp(c,t,ts) as x ->
        begin match find_opt c with
        | Some { tavalue; taparams; timestamp=time } ->
          let nargs = 1 + List.length ts in
          if taparams > nargs then
            error ~loc ("type abbreviation " ^ Symbols.show compiler_state c ^ " needs " ^
              string_of_int taparams ^ " arguments, only " ^
              string_of_int nargs ^ " are provided");
          error_undefined ttime time c tavalue;
          aux time (beta tavalue.ttype (t::ts))
        | None ->
          let t1 = aux seen t in
          let ts1 = smart_map (aux seen) ts in
          if t1 == t && ts1 == ts then x
          else TApp(c,t1,ts1)
        end
    | TPred (f, l) -> TPred (f, List.map (fun (a, b) -> a, aux seen b) l)
    | TArr (a, b) -> TArr (aux seen a, aux seen b)
    | TCData _ as a -> a
    | TLam a -> TLam (aux seen a)
  in
    { ttype = aux ttime ttype; tloc; tamap }


let term_of_ast ~depth state text =
 if State.get D.while_compiling state then
   anomaly ("term_of_ast cannot be used at compilation time");
 let module P = (val option_get ~err:"No parser" (State.get parser state)) in
 let loc = Ast.Loc.initial "(string_of_term)" in
 let t = P.goal ~loc ~text in
 let state, (t,nargs) = ToDBL.temporary_compilation_at_runtime (fun s x ->
    let s, x = ToDBL.query_preterm_of_ast ~depth F.Map.empty s x in
    let s, t = stack_term_of_preterm ~depth s x in
    s, (t, x.amap.nargs)
    ) state t in
 let env = Array.make nargs D.dummy in
 let argsdepth = depth in
 state, R.move ~argsdepth ~from:depth ~to_:depth env t
;;

let is_functional = function TPred (b,_) -> b | _ -> false

let static_check ~exec ~checker:(state,program)
  ({ WithMain.types; type_abbrevs; modes; initial_depth; compiler_state } as q) =
  let time = `Compiletime in
  let state, p,q = quote_syntax time state q in

  (* C.Map.iter (fun k ((v:type_abbrev_declaration),t) -> Format.printf "H %s %a %d\n%!" (Symbols.show state k)
    pp_term v.tavalue.term t) type_abbrevs; *)

  (* Building type abbrev list *)
  let state, talist =
    C.Map.bindings type_abbrevs |>
    map_acc (fun state (name, { tavalue; timestamp=ttime } ) ->
      let tavaluet = unfold_type_abbrevs ~is_typeabbrev:true ~compiler_state initial_depth type_abbrevs tavalue ttime in
      let state, tavaluet = quote_pretype time ~compiler_state state tavaluet in
      state, App(colonec, D.C.of_string (Symbols.show compiler_state name), [lam2forall tavaluet])) state
  in

  (* Building types and functionality *)
  let state, tlist, functionality = C.Map.fold estract_info_from_types types (state,[],[]) in
  let tlist = List.concat (List.rev tlist) in
  
  (* Building modes *)
  let arg_mode2bool = function Input -> Const truec | Output -> Const falsec in

  let rec mode2elpi = function
    | D.Fo b -> App(modefoc,arg_mode2bool b,[])
    | D.Ho (b, l) -> App(modehoc,arg_mode2bool b,[R.list_to_lp_list @@ List.map mode2elpi l]) in

  let state, modes = C.Map.fold (fun tname v (state,tl) -> 
    let state, c = mkQCon time ~compiler_state state ~on_type:false tname in
    let m = List.map mode2elpi v in
    state, (App(pairc, c, [R.list_to_lp_list m])) :: tl) modes (state,[]) in

  let loc = Loc.initial "(static_check)" in
  let args = q :: List.map R.list_to_lp_list [tlist; talist; modes; functionality] in
  let query =
    query_of_term (state, program) (fun ~depth state ->
      assert(depth=0);
      state, (loc,App(checkc,R.list_to_lp_list p, args)), []) in
  let executable = optimize_query query in
  exec executable <> Failure
;;
 *)
 let static_check ~exec ~checker:(state,program) q = true
let term_of_ast ~depth state text = assert false
let quote_syntax time new_state _ = assert false
let is_Arg _ _ = false
let get_Arg _ ~name:_ ~args:_ = assert false
let get_Args _ = assert false
let mk_Arg _ ~name:_ ~args:_ = assert false

let lp ~depth state loc s = assert false
let relocate_closed_term ~from:_ ~to_:_ _ = assert false
let lookup_query_predicate _ _ = assert false