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

let elpi_language = Compiler_data.elpi_language

let error ?loc msg = raise (CompileError(loc, msg))

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
  val equal : table -> table -> bool

  val empty : unit -> table
  val allocate_global_symbol     : D.State.t -> table -> F.t -> table * (D.constant * D.term)
  val allocate_bound_symbol      : D.State.t -> table -> D.constant -> table * D.term
  val get_global_symbol          : table -> F.t -> D.constant option
  val get_canonical              : D.State.t -> table -> D.constant -> D.term
  val global_name : D.State.t -> table -> D.constant -> F.t
  val compile : table -> D.symbol_table

end = struct

  type table = {
    ast2ct : (D.constant * D.term) F.Map.t;
    c2t : D.term D.Constants.Map.t;
    c2s : string D.Constants.Map.t;
    last_global : int;
  }
  [@@deriving show, ord]

  let equal x y = compare x y == 0

  let compile { last_global; c2t; c2s; ast2ct } =
    let t = { D.c2s; c2t = Hashtbl.create (D.Constants.Map.cardinal c2t); frozen_constants = last_global; } in
  (* We could compile the Map c2t to a Hash table upfront, but there is no need
     since it is extended at run time anyway *)
  (* F.Map.iter (fun k (c,v) -> lrt c = c Hashtbl.add t.c2t c v; Hashtbl.add t.c2s c (F.show k)) ast2ct; *)
    t
    

  let allocate_global_symbol_aux x ({ c2t; c2s; ast2ct; last_global } as table) =
    try table, F.Map.find x ast2ct
    with Not_found ->
      let last_global = last_global - 1 in
      let n = last_global in
      let xx = D.Term.Const n in
      let p = n,xx in
      let c2t = D.Constants.Map.add n xx c2t in
      let ast2ct = F.Map.add x p ast2ct in
      let c2s = D.Constants.Map.add n (F.show x) c2s in
      { c2t; c2s; ast2ct; last_global }, p

  let get_global_symbol { ast2ct } s =
    try
      Some (fst @@ F.Map.find s ast2ct)
    with Not_found ->
      None

  let empty () =
    if not @@ D.Global_symbols.table.locked then
      anomaly "SymbolMap created before Global_symbols.table is locked";
  let table = {
    ast2ct = D.Global_symbols.(table.s2ct);
    last_global = D.Global_symbols.table.last_global;
    c2s = D.Global_symbols.table.c2s;
    c2t = D.Constants.Map.map (fun s ->
      let s = F.from_string s in
      let _, t = F.Map.find s D.Global_symbols.(table.s2ct) in
      t) D.Global_symbols.(table.c2s);
  } in
  (*T2.go allocate_global_symbol_aux*) table
    
  let allocate_global_symbol state table x =
    if not (D.State.get D.while_compiling state) then
      anomaly ("global symbols can only be allocated during compilation");
    allocate_global_symbol_aux x table

  let allocate_bound_symbol_aux n ({ c2t; ast2ct } as table) =
    try table, D.Constants.Map.find n c2t
    with Not_found ->
      let xx = D.Term.Const n in
      let c2t = D.Constants.Map.add n xx c2t in
      { table with c2t; ast2ct }, xx

  let allocate_bound_symbol state table n =
    if not (D.State.get D.while_compiling state) then
      anomaly "bound symbols can only be allocated during compilation";
    if n < 0 then
      anomaly "bound variables are positive";
    allocate_bound_symbol_aux n table
  ;;

  let get_canonical state table c =
    if not (D.State.get D.while_compiling state) then
      anomaly "get_canonical can only be used during compilation";
    try D.Constants.Map.find c table.c2t
    with Not_found -> anomaly ("unknown symbol " ^ string_of_int c)

  let global_name state table c =
    if not (D.State.get D.while_compiling state) then
      anomaly "get_canonical can only be used during compilation";
    try F.from_string @@ D.Constants.Map.find c table.c2s
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

open Compiler_data

(* type block_constraint = {
   clique : constant list;
   ctx_filter : constant list;
   rules : prechr_rule list
}
[@@deriving show, ord] *)
  
module TypeChecker : sig

  type type_abbrevs = (TypeAssignment.skema_w_id * Loc.t) F.Map.t
  type arities = Arity.t F.Map.t
  val check_disjoint : type_abbrevs:ScopedTypeExpression.t F.Map.t -> kinds:arities -> unit

  val check_type : type_abbrevs:type_abbrevs -> kinds:arities -> ScopedTypeExpression.t -> TypeAssignment.skema_w_id
  val check_types : type_abbrevs:type_abbrevs -> kinds:arities -> TypeList.t -> TypeAssignment.overloaded_skema_with_id

  type env = TypeAssignment.overloaded_skema_with_id F.Map.t
  (* type env_undeclared = TypeAssignment.t F.Map.t *)
  val check : type_abbrevs:type_abbrevs-> kinds:arities -> types:env -> ScopedTerm.t -> exp:TypeAssignment.t -> bool
  val unknown_type_assignment : string -> TypeAssignment.t

end = struct
  type type_abbrevs = (TypeAssignment.skema_w_id * Loc.t) F.Map.t
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
      let arity = TypeAssignment.nparams @@ fst @@ F.Map.find c type_abbrevs in
      if arity != nargs then
        error ~loc (Format.asprintf "Type %a expects %d arguments but was given %d" F.pp c arity nargs)
    end else
      error ~loc ("Unknown type " ^ F.show c)

  let rec check_loc_tye ~type_abbrevs ~kinds ctx { loc; it } =
    check_tye ~loc ~type_abbrevs ~kinds ctx it
  and check_tye ~loc ~type_abbrevs ~kinds ctx = function
    | Any -> TypeAssignment.Any
    | Const(Bound _,c) -> check_param_exists ~loc c ctx; UVar c
    | Const(Global _,c) -> check_global_exists ~loc c type_abbrevs kinds 0; Cons c
    | App(c,x,xs) ->
        check_global_exists ~loc c type_abbrevs kinds (1 + List.length xs);
        App(c,check_loc_tye ~type_abbrevs ~kinds ctx x, List.map (check_loc_tye ~type_abbrevs ~kinds ctx) xs)
    | Arrow(v,s,t) -> Arr(v,check_loc_tye ~type_abbrevs ~kinds ctx s,check_loc_tye ~type_abbrevs ~kinds ctx t)
    | Pred(_,[]) -> Prop
    | Pred(f,(_,x)::xs) -> Arr(NotVariadic,check_loc_tye ~type_abbrevs ~kinds ctx x,check_tye ~type_abbrevs ~kinds ~loc ctx (Pred(f,xs)))


  let check_type ~type_abbrevs ~kinds ~loc ctx x : TypeAssignment.skema_w_id =
    (* Format.eprintf "check_type under %a\n%!" (F.Map.pp (fun fmt (n,_) -> ())) arities;  *)
    (* Format.eprintf "check_type %a\n%!" ScopedTypeExpression.pp_v_ x;  *)
    let rec aux_params ~loc ctx = function
      | Lam(c,t) ->
          check_param_unique ~loc c ctx;
          TypeAssignment.Lam(c,aux_params ~loc (F.Set.add c ctx) t)
      | Ty t -> TypeAssignment.Ty(check_loc_tye ~type_abbrevs ~kinds ctx t)
    in
      Scope.fresh_type_decl_id (), aux_params ~loc ctx x

  let check_types  ~type_abbrevs ~kinds lst : TypeAssignment.overloaded_skema_with_id =
    match List.map (fun { value; loc } -> check_type ~type_abbrevs ~kinds ~loc F.Set.empty value) lst with
    | [] -> assert false
    | [x] -> TypeAssignment.Single x
    | xs -> TypeAssignment.Overloaded xs

  let check_type  ~type_abbrevs ~kinds { value; loc } : (TypeAssignment.skema_w_id) =
    check_type ~type_abbrevs ~kinds ~loc F.Set.empty value

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
  
  type env = TypeAssignment.overloaded_skema_with_id F.Map.t

  open ScopedTerm

  let error_not_a_function ~loc c args x =
    let t =
      if args = [] then ScopedTerm.Const(Scope.mkGlobal ~escape_ns:true (),c)
      else ScopedTerm.(App(Scope.mkGlobal ~escape_ns:true (),c,List.hd args, List.tl args)) in
    let msg = Format.asprintf "@[<hov>%a is not a function but it is passed the argument@ @[<hov>%a@]@]" ScopedTerm.pretty_ t ScopedTerm.pretty x in
    error ~loc msg

  let pp_tyctx fmt = function
    | None -> Format.fprintf fmt "its context"
    | Some c -> Format.fprintf fmt "%a" F.pp c

  let error_bad_cdata_ety ~loc ~tyctx ~ety c tx =
    let msg = Format.asprintf "@[<hov>literal \"%a\" has type %a@ but %a expects a term of type@ %a@]"  CData.pp c TypeAssignment.pretty tx pp_tyctx tyctx TypeAssignment.pretty ety in
    error ~loc msg
  
  let error_bad_ety ~loc ~tyctx ~ety pp c tx =
    let msg = Format.asprintf "@[<hov>%a has type %a@ but %a expects a term of type@ %a@]"  pp c TypeAssignment.pretty tx pp_tyctx tyctx TypeAssignment.pretty ety in
    error ~loc msg

  let error_bad_ety2 ~loc ~tyctx ~ety1 ~ety2 pp c tx =
    let msg = Format.asprintf "@[<hov>%a has type %a@ but %a expects a term of type@ %a@ or %a@]"  pp c TypeAssignment.pretty tx pp_tyctx tyctx TypeAssignment.pretty ety1 TypeAssignment.pretty ety2 in
    error ~loc msg

  let error_bad_function_ety ~loc ~tyctx ~ety c t =
    let msg = Format.asprintf "@[<hov>%a is a function@ but %a expects a term of type@ %a@]"  ScopedTerm.pretty_ ScopedTerm.(Lam(c,None,t)) pp_tyctx tyctx TypeAssignment.pretty ety in
    error ~loc msg
  
  let error_bad_const_ety_l ~loc ~tyctx ~ety c txl =
    let msg = Format.asprintf "@[<hv>%a is overloaded but none of its types matches the type expected by %a:@,  @[<hov>%a@]@,Its types are:@,@[<v 2>  %a@]@]" F.pp c pp_tyctx tyctx TypeAssignment.pretty ety (pplist ~boxed:true (fun fmt (_,x)-> Format.fprintf fmt "%a" TypeAssignment.pretty x) ", ") txl in
    error ~loc msg

  let error_overloaded_app ~loc ~ety c args alltys =
    let ty = arrow_of_args args ety in
    let msg = Format.asprintf "@[<v>%a is overloaded but none of its types matches:@,  @[<hov>%a@]@,Its types are:@,@[<v 2>  %a@]@]" F.pp c TypeAssignment.pretty ty (pplist (fun fmt (_,x)-> Format.fprintf fmt "%a" TypeAssignment.pretty x) ", ") alltys in
    error ~loc msg
   
  let error_overloaded_app_tgt ~loc ~ety c =
    let msg = Format.asprintf "@[<v>%a is overloaded but none of its types matches make it build a term of type @[<hov>%a@]@]" F.pp c TypeAssignment.pretty ety in
    error ~loc msg
  

  let error_not_poly ~loc c ty sk =
    error ~loc (Format.asprintf "@[<hv>this rule imposes on %a the type@ %a@ is less general than the declared one@ %a@]"
      F.pp c
      TypeAssignment.pretty ty
      TypeAssignment.pretty sk)

  type ret = TypeAssignment.t MutableOnce.t TypeAssignment.t_
  type ret_id = int * TypeAssignment.t MutableOnce.t TypeAssignment.t_
  type spilled_phantoms = ScopedTerm.t list

  let check_no_unknown_global = function
    | None -> ()
    | Some(loc,_,c,ty) ->
        error ~loc (Format.asprintf "@[<v>Unknown global: %a@;Inferred type: %a@]" F.pp c TypeAssignment.pretty ty)

  let local_type ctx ~loc c : ret_id TypeAssignment.overloading =
    try TypeAssignment.Single (0, Scope.Map.find c ctx) (* local types have no id, 0 is given by default *)
    with Not_found -> anomaly ~loc "free variable"

  type classification =
    | Simple of { srcs : ret list; tgt : ret }
    | Variadic of { srcs : ret list; tgt : ret }
    | Unknown

  let rec classify_arrow = function
    | TypeAssignment.Arr(Variadic,x,tgt) -> Variadic { srcs = [x]; tgt }
    | UVar m when MutableOnce.is_set m -> classify_arrow (TypeAssignment.deref m)
    | (App _ | Prop | Cons _ | Any | UVar _) as tgt -> Simple { srcs = []; tgt }
    | TypeAssignment.Arr(NotVariadic,x,xs) ->
        match classify_arrow xs with
        | Simple {srcs; tgt } -> Simple { srcs = x :: srcs; tgt }
        | Unknown -> Unknown
        | Variadic { srcs; tgt } -> Variadic { srcs = x :: srcs; tgt }

  let mk_uvar =
    let i = ref 0 in
    fun s -> incr i; TypeAssignment.UVar(MutableOnce.make (F.from_string (s ^ string_of_int !i)))

  let unknown_type_assignment s = TypeAssignment.Val (mk_uvar s)

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

  let silence_linear_warn f =
    let s = F.show f in
    let len = String.length s in
    len > 0 && (s.[0] = '_' || s.[len-1] = '_')

  let check ~type_abbrevs ~kinds ~types:env (t : ScopedTerm.t) ~(exp : TypeAssignment.t) =
    (* Format.eprintf "============================ checking %a\n" ScopedTerm.pretty t; *)
    let needs_spill = ref false in
    let sigma : (TypeAssignment.t * int * Loc.t) F.Map.t ref = ref F.Map.empty in
    let unknown_global = ref None in
    let fresh_name = let i = ref 0 in fun () -> incr i; F.from_string ("%dummy"^ string_of_int !i) in
    (* let set_fresh_id = let i = ref 0 in fun x -> incr i; x := Some !i in *)

    let rec check (ctx : ret Scope.Map.t) ~loc ~tyctx x ety : spilled_phantoms =
      (* Format.eprintf "@[<hov 2>checking %a : %a@]\n" ScopedTerm.pretty_ x TypeAssignment.pretty ety; *)
      match x with
      | Impl(b,t1,t2) -> check_impl ctx ~loc ~tyctx b t1 t2 ety
      | Const(Global _ as gid,c) -> check_global ctx ~loc ~tyctx (gid,c) ety
      | Const(Bound lang,c) -> check_local ctx ~loc ~tyctx (c,lang) ety
      | CData c -> check_cdata ~loc ~tyctx kinds c ety
      | Spill(_,{contents = (Main _ | Phantom _)}) -> assert false
      | Spill(sp,info) -> check_spill ctx ~loc ~tyctx sp info ety
      | App(Global _ as gid,c,x,xs) -> check_app ctx ~loc ~tyctx (c,gid) (global_type env ~loc c) (x::xs) ety 
      | App(Bound lang as gid,c,x,xs) -> check_app ctx ~loc ~tyctx (c,gid) (local_type ctx ~loc (c,lang)) (x::xs) ety
      | Lam(c,cty,t) -> check_lam ctx ~loc ~tyctx c cty t ety
      | Discard -> []
      | Var(c,args) -> check_app ctx ~loc ~tyctx (c, Bound elpi_language (*hack*)) (uvar_type ~loc c) args ety
      | Cast(t,ty) ->
          let ty = TypeAssignment.subst (fun f -> Some (TypeAssignment.UVar(MutableOnce.make f))) @@ check_loc_tye ~type_abbrevs ~kinds F.Set.empty ty in
          let spills = check_loc ctx ~tyctx:None t ~ety:ty in
          if unify ty ety then spills
          else error_bad_ety ~loc ~tyctx ScopedTerm.pretty_ x ty ~ety

    and resolve_gid id = function
      | Scope.Global x -> x.decl_id <- id
      | _ -> ()

    and global_type env ~loc c : ret_id TypeAssignment.overloading =
      try TypeAssignment.fresh_overloaded @@ F.Map.find c env
      with Not_found ->
        match !unknown_global with
        | None ->
            let ty = mk_uvar (Format.asprintf "Unknown_%a" F.pp c) in
            let id = Scope.fresh_type_decl_id () in
            unknown_global := Some (loc,id,c,ty);
            Single (id,ty)
        | Some(_,id,c',ty) when F.equal c c' -> Single (id,ty)
        | Some _ -> error ~loc (Format.asprintf "Unknown global: %a" F.pp c)
        
    and check_impl ctx ~loc ~tyctx b t1 t2 ety =
      if not @@ unify (ety) Prop then error_bad_ety ~loc ~tyctx ~ety:Prop ScopedTerm.pretty_ (Impl(b,t1,t2)) (ety)
      else
        let lhs, rhs,c (* of => *) = if b then t1,t2,F.implf else t2,t1,F.rimplf in
        let spills = check_loc ~tyctx:(Some c) ctx rhs ~ety:Prop in
        let lhs_ty = mk_uvar (Format.asprintf "LHSty_%a" F.pp c) in
        let more_spills = check_loc ~tyctx:None ctx ~ety:lhs_ty lhs in
        let ety1 = TypeAssignment.Prop in
        let ety2 = TypeAssignment.App(F.from_string "list",Prop,[]) in
        if try_unify lhs_ty ety1 then spills @ more_spills (* probably an error if not empty *)
        else if unify lhs_ty (ety2) then spills @ more_spills (* probably an error if not empty *)
        else error_bad_ety2 ~tyctx:(Some c) ~loc ~ety1 ~ety2  ScopedTerm.pretty lhs lhs_ty

    and check_global ctx ~loc ~tyctx (gid,c) ety =
      match global_type env ~loc c with
      | Single (id,ty) ->
          if unify ty ety then (resolve_gid id gid; [])
          else error_bad_ety ~tyctx ~loc ~ety F.pp c ty
      | Overloaded l ->
          if unify_first gid l ety then []
          else error_bad_const_ety_l ~tyctx ~loc ~ety c l

    and check_local ctx ~loc ~tyctx c ety =
      match local_type ctx ~loc c with
      | Single (id,ty) ->
          if unify ty ety then []
          else error_bad_ety ~tyctx ~loc ~ety F.pp (fst c) ty
      | Overloaded _ -> assert false

    and check_cdata ~loc ~tyctx kinds c ety =
      let name = F.from_string @@ CData.name c in
      check_global_exists ~loc name type_abbrevs kinds 0;
      let ty = TypeAssignment.Cons name in
      if unify ty ety then []
      else error_bad_cdata_ety ~tyctx ~loc c ty ~ety

    and check_lam ctx ~loc ~tyctx c cty t ety =
      let name_lang = match c with Some c -> c | None -> fresh_name (), elpi_language in
      let src = match cty with
        | None -> mk_uvar "Src"
        | Some x -> 
           TypeAssignment.subst (fun f -> Some (TypeAssignment.UVar(MutableOnce.make f))) @@ check_loc_tye ~type_abbrevs ~kinds F.Set.empty x in
      let tgt = mk_uvar "Tgt" in
      (* let () = Format.eprintf "lam ety %a\n" TypeAssignment.pretty ety in *)
      if unify (TypeAssignment.Arr(Ast.Structured.NotVariadic,src,tgt)) ety then
        (* let () = Format.eprintf "add to ctx %a : %a\n" F.pp name TypeAssignment.pretty src in *)
        check_loc ~tyctx (Scope.Map.add name_lang src ctx) t ~ety:tgt
      else
        error_bad_function_ety ~loc ~tyctx ~ety c t

    and check_spill ctx ~loc ~tyctx sp info ety =
      needs_spill := true;
      let inner_spills = check_spill_conclusion_loc ~tyctx:None ctx sp ~ety:(TypeAssignment.Arr(Ast.Structured.NotVariadic,ety,mk_uvar "Spill")) in
      assert(inner_spills = []);
      let phantom_of_spill_ty i ty =
        { loc; it = Spill(sp,ref (Phantom(i+1))); ty = MutableOnce.create (TypeAssignment.Val ty) } in
      match classify_arrow (ScopedTerm.type_of sp) with
      | Simple { srcs; tgt } ->
          if not @@ unify tgt Prop then error ~loc "only predicates can be spilled";
          let spills = srcs in
          if spills = [] then
            error ~loc "nothing to spill, the expression lacks no arguments";
          let (first_spill) = List.hd spills in
          if unify first_spill ety then begin
            info := Main (List.length spills);
            List.mapi phantom_of_spill_ty @@ List.tl spills
          end
          else error_bad_ety ~tyctx ~loc ~ety ScopedTerm.pretty_ (Spill(sp,info)) first_spill
      | _ -> error ~loc "hard spill"

    and unify_tgt_ety n ety (_,t) = 
      match classify_arrow t with
      | Unknown -> true
      | Simple { srcs; tgt } ->
          let nsrcs = List.length srcs in
          if n > nsrcs then false
          else
            let rec drop i l = if i = 0 then l else drop (i-1) (List.tl l) in
            let srcs = drop n srcs in try_unify (arrow_of_tys srcs tgt) ety
      | Variadic _ -> true (* TODO *)

    and check_app ctx ~loc ~tyctx (c,cid) cty args ety =
      match cty with
      | Overloaded l ->
        (* Format.eprintf "options %a %a %d: %a\n" F.pp c TypeAssignment.pretty ety (List.length args) (pplist TypeAssignment.pretty "; ") l; *)
        let l = List.filter (unify_tgt_ety (List.length args) ety) l in
        begin match l with
        | [] -> error_overloaded_app_tgt ~loc ~ety c
        | [ty] -> check_app ctx ~loc ~tyctx (c,cid) (Single ty) args ety
        | l ->
        (* Format.eprintf "newoptions: %a\n" (pplist TypeAssignment.pretty "; ") l; *)
            let args = List.concat_map (fun x -> x :: check_loc ~tyctx:None ctx ~ety:(mk_uvar (Format.asprintf "Ety_%a" F.pp c)) x) args in
            let targs = List.map ScopedTerm.type_of args in
            check_app_overloaded ctx ~loc (c,cid) ety args targs l l
        end
      | Single (id,ty) ->
          let err ty =
            if args = [] then error_bad_ety ~loc ~tyctx ~ety F.pp c ty (* uvar *)
            else error_bad_ety ~loc ~tyctx ~ety ScopedTerm.pretty_ (App(Scope.mkGlobal ~escape_ns:true ()(* sucks *),c,List.hd args,List.tl args)) ty in
          let monodirectional () =
            (* Format.eprintf "checking app mono %a\n" F.pp c; *)
            let tgt = check_app_single ctx ~loc c ty [] args in
            if unify tgt ety then (resolve_gid id cid; [])
            else err tgt in
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
              let _ = check_app_single ctx ~loc c ty [] args in (resolve_gid id cid; [])
            else err rest_tgt in
          match classify_arrow ty with
          | Unknown | Variadic _ -> monodirectional ()
          | Simple { srcs; tgt } ->
            if List.length args > List.length srcs then monodirectional () (* will error *)
            else
              if any_arg_is_spill args then monodirectional ()
              else bidirectional srcs tgt

    (* REDO PROCESSING ONE SRC at a time *)
    and check_app_overloaded ctx ~loc (c, id) ety args targs alltys = function
      | [] -> error_overloaded_app ~loc c args ~ety alltys
      | (_,t)::ts ->
          (* Format.eprintf "checking overloaded app %a\n" F.pp c; *)
          match classify_arrow t with
          | Unknown -> error ~loc (Format.asprintf "Type too ambiguous to be assigned to the overloaded constant: %s for type %a" (F.show c) TypeAssignment.pretty t)
          | Simple { srcs; tgt } ->
              if try_unify (arrow_of_tys srcs tgt) (arrow_of_tys targs ety) then [] (* TODO: here we should something ? *)
              else check_app_overloaded ctx ~loc (c, id) ety args targs alltys ts
          | Variadic { srcs ; tgt } ->
              let srcs = extend srcs targs in
              if try_unify (arrow_of_tys srcs tgt) (arrow_of_tys targs ety) then [] (* TODO: here we should something ? *)
              else check_app_overloaded ctx ~loc (c, id) ety args targs alltys ts

    and check_app_single ctx ~loc c ty consumed args =
      match args with
      | [] -> ty
      | x :: xs ->
        (* Format.eprintf "checking app %a @ %a\n" F.pp c ScopedTerm.pretty x; *)
        match ty with
          | TypeAssignment.Arr(Variadic,s,t) ->
              let xs = check_loc_if_not_phantom ~tyctx:(Some c) ctx x ~ety:s @ xs in
              if xs = [] then t else check_app_single ctx ~loc c ty (x::consumed) xs
          | Arr(NotVariadic,s,t) ->
              let xs = check_loc_if_not_phantom ~tyctx:(Some c) ctx x ~ety:s @ xs in
              check_app_single ctx ~loc c t (x::consumed) xs
          | Any -> check_app_single ctx ~loc c ty (x::consumed) xs
          | UVar m when MutableOnce.is_set m ->
              check_app_single ctx ~loc c (TypeAssignment.deref m) consumed (x :: xs)
          | UVar m ->
              let s = mk_uvar "Src" in
              let t = mk_uvar "Tgt" in
              let _ = unify ty (TypeAssignment.Arr(Ast.Structured.NotVariadic,s,t)) in
              check_app_single ctx ~loc c ty consumed (x :: xs)
          | Cons c when F.Map.mem c type_abbrevs ->
              let ty = TypeAssignment.apply (fst @@ F.Map.find c type_abbrevs) [] in
              check_app_single ctx ~loc c ty consumed args
          | App(c,x,xs) when F.Map.mem c type_abbrevs ->
              let ty = TypeAssignment.apply (fst @@ F.Map.find c type_abbrevs) (x::xs) in
              check_app_single ctx ~loc c ty consumed args
          | _ -> error_not_a_function ~loc:x.loc c (List.rev consumed) x (* TODO: trim loc up to x *)

    and check_loc ~tyctx ctx { loc; it; ty } ~ety : spilled_phantoms =
      (* if MutableOnce.is_set ty then []
      else *)
        begin
          (* assert (not @@ MutableOnce.is_set ty); *)
          let extra_spill = check ~tyctx ctx ~loc it ety in
          if not @@ MutableOnce.is_set ty then MutableOnce.set ty (Val ety);
          extra_spill
        end

    and check_loc_if_not_phantom ~tyctx ctx x ~ety : spilled_phantoms =
      match x.it with
      | Spill(_,{ contents = Phantom _}) -> []
      | _ -> check_loc ~tyctx ctx x ~ety

    and check_spill_conclusion_loc ~tyctx ctx { loc; it; ty } ~ety : spilled_phantoms =
      assert (not @@ MutableOnce.is_set ty);
      let extra_spill = check_spill_conclusion ~tyctx ctx ~loc it ety in
      MutableOnce.set ty (Val ety);
      extra_spill

    (* This descent to find the spilled term is a bit ad hoc, since it
    inlines => and , typing... but leaves the rest of the code clean *)
    and check_spill_conclusion ~tyctx ctx ~loc it ety =
      match it with
      | Impl(true,x,y) ->
          let lhs = mk_uvar "LHS" in
          let spills = check_loc ~tyctx ctx x ~ety:lhs in
          if spills <> [] then error ~loc "Hard spill";
          if try_unify lhs Prop || try_unify lhs (App(F.from_string "list",Prop,[]))
          then check_spill_conclusion_loc ~tyctx ctx y ~ety
          else error ~loc "Bad impl in spill"
      | App(Global _ as g,c,x,xs) when F.equal c F.andf ->
          let spills = check_loc ~tyctx ctx x ~ety:Prop in
          if spills <> [] then error ~loc "Hard spill";
          begin match xs with
          | [] -> assert false
          | [x] -> check_loc ~tyctx ctx x ~ety
          | x::xs -> check_spill_conclusion ~tyctx ctx ~loc (App(g,c,x,xs)) ety
          end
      | _ -> check ~tyctx ctx ~loc it ety

    and check_matches_poly_skema_loc { loc; it } =
      let c, args =
        let rec head it =
          match it with
          | App(Global _,f,{ it = Lam(_,_,x) },[]) when F.equal F.pif f -> head x.it
          | Impl(false,{ it = App(Global _,c',x,xs) },_) -> c', x :: xs
          | Impl(false,{ it = Const(Global _,c') },_) -> c', []
          | App(Global _,c,x,xs) -> c, x :: xs
          | Const(Global _,c) -> c, []
          | _ ->
            (* Format.eprintf "%a" ScopedTerm.pretty_ it; *)
            assert false in
        head it in
      (* Format.eprintf "Checking %a\n" F.pp c; *)
      match F.Map.find c env with
      | Single (_id,Ty _) -> () (* TODO: Should use id? *)
      | Single (_id, Lam _ as sk) -> check_matches_poly_skema ~loc ~pat:(TypeAssignment.fresh sk) c (arrow_of_args args Prop) (* TODO: should use id? *)
      | Overloaded _ -> ()

    and check_matches_poly_skema ~loc ~pat c ty =
      if try_matching ~pat ty then () else error_not_poly ~loc c ty (fst pat |> snd)

    and try_unify x y =
      let vx = TypeAssignment.vars_of (Val x) in
      let vy = TypeAssignment.vars_of (Val y) in
      let b = unify x y in
      if not b then (undo vx; undo vy);
      b
    
    and unify_first gid l ety =
      let vars = TypeAssignment.vars_of (Val ety) in
      let rec aux = function
        | [] -> false
        | (id, x)::xs -> if unify x ety then (resolve_gid id gid; true) else (undo vars; aux xs)
      in
        aux l
  
    and undo = function
      | [] -> ()
      | m :: ms -> MutableOnce.unset m; undo ms

    and uvar_type ~loc c =
      try
        let ty, nocc, loc = F.Map.find c !sigma in
        sigma := F.Map.add c (ty,nocc+1,loc) !sigma;
        Single (0, TypeAssignment.unval @@ ty) (* TODO: not sure of this... *)
      with Not_found ->
        let ty = TypeAssignment.UVar (MutableOnce.make c) in
        sigma := F.Map.add c (TypeAssignment.Val ty,1,loc) !sigma;
        Single (0, ty) (* TODO: not sure of this... *)
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
      | Arr(Variadic,_,t), _ -> unif ~matching t t2
      | _, Arr(Variadic,_,t) -> unif ~matching t1 t
      | UVar m, UVar n when matching -> assign m t2
      | UVar m, _ when not matching -> assign m t2
      | _, UVar m -> assign m t1
      | Cons c, _ when F.Map.mem c type_abbrevs ->
          let t1 = apply (fst @@ F.Map.find c type_abbrevs) [] in
          unif ~matching t1 t2
      | _, Cons c when F.Map.mem c type_abbrevs ->
          let t2 = apply (fst @@ F.Map.find c type_abbrevs) [] in
          unif ~matching t1 t2
      | App(c,x,xs), _ when F.Map.mem c type_abbrevs ->
          let t1 = apply (fst @@ F.Map.find c type_abbrevs) (x::xs) in
          unif ~matching t1 t2
      | _, App(c,x,xs) when F.Map.mem c type_abbrevs ->
          let t2 = apply (fst @@ F.Map.find c type_abbrevs) (x::xs) in
          unif ~matching t1 t2
      | _,_ -> false

    and unify x (y: TypeAssignment.t MutableOnce.t TypeAssignment.t_) = unif ~matching:false x y
    and try_matching ~pat:((_,x),vars) y =
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
      (* TODO HACK since typing is done too late, the same unit should be checked only once *)
      if MutableOnce.is_set t.ty then false else

      let spills = check_loc ~tyctx:None Scope.Map.empty t ~ety:(TypeAssignment.unval exp) in
      check_no_unknown_global !unknown_global;
      check_matches_poly_skema_loc t;
      if spills <> [] then error ~loc:t.loc "cannot spill in head";
      F.Map.iter (fun k (_,n,loc) ->
        if n = 1 && not @@ silence_linear_warn k then warn ~loc (Format.asprintf "%a is linear: name it _%a (discard) or %a_ (fresh variable)"
          F.pp k F.pp k F.pp k)) !sigma;
      !needs_spill

  (* let check ~type_abbrevs a b c =
    try check ~type_abbrevs a b c with
    | CompileError(_,"Unknown global: %spill") -> Printf.eprintf "SPILLING"; exit 1
    | CompileError(_,s) when Re.Str.(string_match (regexp "Unknown global: @")) s 0 -> Printf.eprintf "MACRO"; exit 1
    | CompileError(loc,msg) -> Format.eprintf "Ignoring type error: %a %s\n" (Util.pp_option Loc.pp) loc msg; TypeAssignment.(Val Prop) *)
end

module FunctionalityChecker : sig 
  type func_map = Functionality.t F.Map.t

  val check_clause : loc:Loc.t -> functional_preds:func_map -> 
    ScopedTerm.t -> unit

  val merge_types_and_abbrevs :
    old:func_map -> 
    type_abbrevs:(F.t * ScopedTypeExpression.t) list -> 
    types:TypeList.t F.Map.t -> func_map

  val merge : func_map -> func_map -> func_map

  val pp : Format.formatter -> func_map -> unit
end = struct 

  exception StopCheck

  open Functionality
  module STE = ScopedTypeExpression
  type t = Functionality.t
  type f = Functionality.f

  type func_map = t F.Map.t
  type v_ = STE.v_
  type t_ = STE.t_

  let rec functionalities_leq l1 l2 = match l1, l2 with
    | _, [] -> true (* l2 can be any length (due to partial application) *)
    | x::xs, y::ys -> functionality_leq x y && functionalities_leq xs ys
    | [], _ -> error "the first list of functional args is can't been smaller then the second one: type error"

  and functionality_leq a b = match a, b with
    | AssumedFunctional, AssumedFunctional -> true
    | AssumedFunctional, t -> error (Format.asprintf "Cannot compare %a with %a" pp_f a pp_f b)
    | _, AssumedFunctional -> error (Format.asprintf "Cannot compare %a with %a" pp_f a pp_f b)
    | _, Relational -> true
    | Relational, _ -> false
    | Functional xs, Functional ys -> functionalities_leq xs ys
    | BoundVar _, _ | _, BoundVar _ -> failwith "NYI"

  let rec bvars2relation = function 
    | BoundVar _ -> Relational 
    | Functional l -> Functional (List.map bvars2relation l) 
    | e -> e

  let rec bvars2relation_lam = function
    | Lam (_,b) -> bvars2relation_lam b
    | F (b,_) -> bvars2relation b

  (* TODO: @FissoreD simplify the map: each type is in the map (Relational or not) to avoid
     all of these reduntant find_opt. Since all type are in the map we can
     do find and never get Not_found error *)
  (* TODO: functionality relation of preds: remove lambdas, i.e. replaces bound_vars with Relational *)
  let get_functionality map k = 
    match F.Map.find_opt k map with
    | Some (F (e, _)) -> e
    | None -> Relational
    | Some (Lam _) -> error "not fully applied type_abbrev"

  let get_functionality_bvars map k = 
    match F.Map.find_opt k map with
    | Some e -> bvars2relation_lam e
    | None -> Relational

  (* 
    Invariant every constant in the map is functional:
    i.e. for each k in the domain, map[k] = Functional [...]
  *)
  let is_functional map k = not (get_functionality map k = Relational)

  let map_snd f = List.map (fun (_, STE.{it}) -> f it)

  let rec subst (type_abbrevs:func_map) : f -> f = function
    | BoundVar k as t ->
      begin match F.Map.find_opt k type_abbrevs with
      | None -> t
      | Some (F (f,_)) -> f
      | Some (Lam (_,b)) -> error ~loc:(get_loc b) "type_abbrev not fully applied"
      end
    | Functional l -> Functional (List.map (subst type_abbrevs) l)
    | AssumedFunctional | Relational as t -> t

  let rec bind type_abbrevs : (t*'a) -> f = function
    | Lam (n,b), x::xs -> bind (F.Map.add n (F (x, Loc.initial"")) type_abbrevs) (b,xs)
    | Lam (_,b), [] -> error ~loc:(get_loc b) "type_abbrev is not fully applied"
    | F (t,_), [] -> (subst type_abbrevs t)
    | F (_,loc), _::_ -> anomaly ~loc "type_abbrev is too much applied"

  and type2funct bound_vars (type_abbrevs: func_map) : t_ -> f = function
    | STE.Pred(Function, xs) -> (Functional (map_snd (type2funct bound_vars type_abbrevs) xs))
    | STE.Pred(Relation, xs) -> Relational
    | Const (_,c) when F.Set.mem c bound_vars -> BoundVar c 
    | Const (_,c) -> 
      begin match F.Map.find_opt c type_abbrevs with
        | None -> Relational
        | Some (F f) -> fst f
        | Some (Lam _) -> error "Not fully applied type_abbrev..."
      end
    | Any -> Relational
    | App(c,x,xs) ->
      (* TODO: if we accept polymorphic type with functional arguments, like
        `:functional pred do i:(list (:functional pred))`, then we should extend
        this match *)
      begin match F.Map.find_opt c type_abbrevs with
      | None -> Relational
      | Some c -> 
        let xxs = List.map (fun STE.{it} -> type2funct bound_vars type_abbrevs it) (x::xs) in
        bind type_abbrevs (c, xxs)
      end
    | Arrow (Variadic, _, _) -> AssumedFunctional
    (* TODO: This depends on the last element of Arrow, since we can have:
      :functional pred p i:((:functional pred) -> (:functional pred)).
      which is equivalent to pred p i:(pred o:(:functional pred) o:(:functional pred))
    
    *)
    | Arrow (NotVariadic,_,_) -> Relational

  let rec type2funct_lam bound_vars type_abbrevs : v_ -> t = function
    | Lam (n, t) -> Lam (n, type2funct_lam (F.Set.add n bound_vars) type_abbrevs t)
    | Ty {it;loc} -> F (type2funct bound_vars type_abbrevs it, loc)

  let pp_locs fmt (l: v_ list) =
    let rec go_under_lam = function (Lam (_,x): v_) -> go_under_lam x | Ty {loc} -> loc in
    Format.fprintf fmt "[%a]" (pplist (fun fmt -> Format.fprintf fmt "%a" Loc.pp) ",") (List.map go_under_lam l)

  (** 
    Takes a constant and its type.
    Returns the type if the type is functional
  *)
  let rec map_pred name : STE.t -> (STE.v_) option = function
    | {value = (Ty {it = Pred (Function,_) as it;loc})} -> Some (Ty {it;loc})
    | {value = (Lam (ag,value))} as t -> 
      begin match map_pred name {t with value} with
        | Some e -> Some (Lam (ag,e))
        | None -> None
      end
    | _ -> None

  (**
    Takes a constant name and the list of its types. The list is filtered with
    [map_pred] and of the result we accepts lists of length 
    - 0 -> the type is not functional
    - 1 -> the type is functional
    - N -> the type has multiple functionality definition: we throw an error
  *)
  let map_is_func (func_map: func_map) name (l : STE.t list) =
    match List.filter_map (map_pred name) l with
    | [] -> None (* the type is not functional *)
    | [t] -> Some (type2funct_lam F.Set.empty func_map t) (* the type is functional *)
    | l -> error (Format.asprintf "Type %a has multiple functionality definitions, this is not allowed %a" F.pp name pp_locs l)

  let merge = F.Map.union (fun k _ -> error ("Duplicate functionality declaration for " ^ F.show k))

  let merge_type_list types old =
    merge old (F.Map.filter_map (map_is_func old) types)

  let merge_type_abbrevs type_abbrevs old = 
    let new_ = List.map (fun (x,y) -> x,[y]) type_abbrevs in
    let new_ = F.Map.of_seq (List.to_seq new_) in
    merge_type_list new_ old

  let merge_types_and_abbrevs ~old  ~type_abbrevs ~types =
    merge_type_abbrevs type_abbrevs old |> merge_type_list types

  let functionality_leq_err ~loc c f' f =
    if not (functionality_leq f' f) then
      error ~loc (Format.asprintf "Functionality of %a is %a and is not included in %a" F.pp c pp_f f' pp_f f)

  let rec head_ag_func_pairing functional_preds args fs = 
    let func_vars = ref F.Map.empty in
    let rec aux ~loc f = function
      | ScopedTerm.Const (Global _,c) -> (* Look into type_abbrev for global symbols *)
        let f' = get_functionality functional_preds c in
        functionality_leq_err ~loc c f' f      
      | Const _ -> failwith "TODO"
      | App(_,hd,x,xs) -> 
        let f' = get_functionality functional_preds hd in
        assert (functionality_leq f' f);
        begin match f' with
        | Functional l -> aux' (x::xs) l
        | _ -> ()
        end
      | Impl _ -> error "TODO" (* Example p (a => b) *)
      | Discard -> ()
      | Var (v, ag) ->
        begin match F.Map.find_opt v !func_vars with
        | None -> func_vars := F.Map.add v f !func_vars (* -> First appereance of the variable in the head *)
        | Some f' -> functionality_leq_err ~loc v f' f
        end
      | Lam (None, _type, {it}) -> failwith "TODO"
      | Lam (Some (e,_), _type, {it}) -> failwith "TODO"
      | CData _ -> assert (f = Relational) (* note that this is also true, otherwise we would have a type error *)
      | Spill _ -> error "Spill in the head of a clause forbidden"
      | Cast ({it},_) -> aux ~loc f it
    and aux' args fs = match args, fs with
      | [], [] -> ()
      | ScopedTerm.{it;loc}::xs, y::ys -> aux ~loc y it; aux' xs ys 
      | _ -> failwith "Partial application ??" 
    in
    aux' args fs;
    !func_vars

  and check_head functional_preds func_vars head_name head_args =
    match get_functionality_bvars functional_preds head_name with
    | Relational -> raise StopCheck
    | AssumedFunctional -> raise StopCheck
    | Functional l -> head_ag_func_pairing functional_preds head_args l
    | BoundVar v -> error "unreachable branch"

  and check_body func_vars = func_vars

  let rec check_clause ~loc ~functional_preds func_vars ScopedTerm.{it} =
    match it with
    | Impl(false, hd, body) -> 
      check_clause ~loc ~functional_preds func_vars hd |> check_body
    | App(_,c,x,xs) -> 
      begin
        try check_head functional_preds func_vars c (x::xs)
        with StopCheck -> func_vars 
      end
    | Const (_,_) -> func_vars (* a predicate with arity 0 is functional *)
    | _ -> error ~loc "invalid type"

  let check_clause ~loc ~functional_preds t =
    check_clause ~loc ~functional_preds F.Map.empty t |> ignore

  let pp (fmt: Format.formatter) (e: func_map) : unit =
    F.Map.pp pp fmt e
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

module CheckedFlat = struct

type program = {
  toplevel_macros : macro_declaration;
  kinds : Arity.t F.Map.t;
  types : (TypeAssignment.overloaded_skema_with_id) F.Map.t;
  types_ids : TypeAssignment.skema C.Map.t;
  types_indexing : (Ast.Structured.tattribute option * Loc.t) list F.Map.t;
  type_abbrevs :  (TypeAssignment.skema_w_id * Loc.t) F.Map.t;
  modes : (mode * Loc.t) F.Map.t;
  functional_preds: Functionality.t F.Map.t;
  clauses : (bool * (ScopedTerm.t,Ast.Structured.attribute) Ast.Clause.t) list;
  chr : (F.t,ScopedTerm.t) Ast.Structured.block_constraint list;
  builtins : BuiltInPredicate.t list;
}
[@@deriving show]

end

type unchecked_compilation_unit = {
  version : string;
  code : Flat.program;
}
[@@deriving show]

(* TODO: proper hack *)
let hash_base x = string_of_int @@ Hashtbl.hash x 


type checked_compilation_unit = {
  version : string;
  checked_code : CheckedFlat.program;
  base_hash : string;
  precomputed_kinds : Arity.t F.Map.t;
  precomputed_types : TypeAssignment.overloaded_skema_with_id F.Map.t;
  precomputed_type_abbrevs :  (TypeAssignment.skema_w_id * Loc.t) F.Map.t;
  precomputed_functional_preds : Functionality.t F.Map.t;
  precomputed_types_ids : TypeAssignment.skema C.Map.t;
  type_checking_time : float;
}
[@@deriving show]


module Assembled = struct

type program = {
  (* for printing only *)
  clauses : (Ast.Structured.insertion option * string option * constant * clause) list;

  kinds : Arity.t F.Map.t;
  types : TypeAssignment.overloaded_skema_with_id F.Map.t;
  types_ids : TypeAssignment.skema C.Map.t;
  type_abbrevs : (TypeAssignment.skema_w_id * Loc.t) F.Map.t;
  modes : (mode * Loc.t) F.Map.t;
  functional_preds : Functionality.t F.Map.t;
  total_type_checking_time : float;

  prolog_program : index;
  indexing : (mode * indexing) C.Map.t;
  chr : CHR.t;

  symbols : SymbolMap.table;

  toplevel_macros : macro_declaration;
  hash : string;

}
and attribute = {
  id : string option;
  timestamp : grafting_time;
  insertion : Ast.Structured.insertion option;
}
[@@deriving show]

let empty () = {
  clauses = [];
  kinds = F.Map.empty;
  types = F.Map.add F.mainf TypeAssignment.(Single (-1, (Ty Prop))) F.Map.empty;
  types_ids = C.Map.empty;
  type_abbrevs = F.Map.empty; modes = F.Map.empty; functional_preds = F.Map.empty;
  prolog_program = { idx = Ptmap.empty; time = 0; times = StrMap.empty };
  indexing = C.Map.empty;
  chr = CHR.empty;
  symbols = SymbolMap.empty ();
  toplevel_macros = F.Map.empty;
  total_type_checking_time = 0.0;
  hash = "";
}

end


type builtins = string * Data.BuiltInPredicate.declaration list

type program = State.t * Assembled.program
type header = program


module WithMain = struct

(* The entire program + query, but still in "printable" format *)
type 'a query = {  
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
  val structure_type_expression : Loc.t -> 'a -> (Ast.raw_attribute list -> 'a option) -> Ast.raw_attribute list Ast.TypeExpression.t -> 'a Ast.TypeExpression.t

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
    | TPred(att,p) when valid att <> None -> TPred(Option.get (valid att),List.map (fun (m,p) -> m, structure_type_expression_aux ~loc valid p) p)
    | TPred([], _) -> assert false
    | TPred(a :: _, _) -> error ~loc ("illegal attribute " ^ show_raw_attribute a)
    | TArr(s,t) -> TArr(structure_type_expression_aux ~loc valid s,structure_type_expression_aux ~loc valid t) 
    | TApp(c,x,xs) -> TApp(c,structure_type_expression_aux ~loc valid x,List.map (structure_type_expression_aux ~loc valid) xs)
    | TConst c -> TConst c
  }

  let structure_type_expression loc toplevel_func valid t = 
    match t.TypeExpression.tit with
    | TPred([],p) ->
      { t with tit = TPred(toplevel_func,List.map (fun (m,p) -> m, structure_type_expression_aux ~loc valid p) p) }
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
            types = (*List.rev*) types; (* we prefer the last one *)
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

  let singlequote : (string * QuotationHooks.quotation) option State.component = State.declare
  ~descriptor:elpi_state_descriptor
  ~name:"elpi:singlequote"
  ~pp:(fun _ _ -> ())
  ~clause_compilation_is_over:(fun b -> b)
  ~goal_compilation_begins:(fun b -> b)
  ~goal_compilation_is_over:(fun ~args:_ b -> Some b)
  ~compilation_is_over:(fun x -> Some x)
  ~execution_is_over:(fun x -> Some x)
  ~init:(fun () -> None)

  let backtick  : (string * QuotationHooks.quotation) option State.component = State.declare
  ~descriptor:elpi_state_descriptor
  ~name:"elpi:backtick"
  ~pp:(fun _ _ -> ())
  ~clause_compilation_is_over:(fun b -> b)
  ~goal_compilation_begins:(fun b -> b)
  ~goal_compilation_is_over:(fun ~args:_ b -> Some b)
  ~compilation_is_over:(fun x -> Some x)
  ~execution_is_over:(fun x -> Some x)
  ~init:(fun () -> None)

  let scope_singlequote ~loc state x = 
    match State.get singlequote state with
    | None -> ScopedTerm.(Const(Scope.mkGlobal (),x))
    | Some (language,f) -> ScopedTerm.unlock @@ ScopedTerm.of_simple_term_loc @@ f ~language state loc (F.show x)
  let scope_backtick ~loc state x =
    match State.get backtick state with
    | None -> ScopedTerm.(Const(Scope.mkGlobal (),x))
    | Some (language,f) -> ScopedTerm.unlock @@ ScopedTerm.of_simple_term_loc @@ f ~language state loc (F.show x)
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

type mtm = {
  macros : (ScopedTerm.t * Loc.t) F.Map.t;
  ctx: F.Set.t;
}
let empty_mtm = { macros = F.Map.empty; ctx = F.Set.empty }
let todopp name _fmt _ = error ("pp not implemented for field: "^name)

let get_mtm, set_mtm, drop_mtm, update_mtm =
  let mtm =
    State.declare
     ~name:"elpi:mtm" ~pp:(todopp "elpi:mtm")
     ~descriptor:D.elpi_state_descriptor
     ~clause_compilation_is_over:(fun _ -> empty_mtm)
     ~goal_compilation_begins:(fun x -> x)
     ~goal_compilation_is_over:(fun ~args:_ _ -> None)
      ~compilation_is_over:(fun _ -> assert false)
      ~execution_is_over:(fun _ -> assert false)
      ~init:(fun () -> empty_mtm) in
  State.(get mtm, set mtm, drop mtm, update mtm)

module Scope_Quotation_Macro : sig

  val run : State.t -> toplevel_macros:macro_declaration -> Ast.Structured.program -> State.t * Scoped.program
  val check_duplicate_mode : F.t -> (mode * Loc.t) -> (mode * Loc.t) F.Map.t -> unit
  val scope_loc_term : state:State.t -> Ast.Term.t -> ScopedTerm.t

end = struct
  let map_append k v m =
    try
      let l = F.Map.find k m in
      F.Map.add k (TypeList.merge v l) m
    with Not_found ->
      F.Map.add k v m

  let is_uvar_name f =  F.is_uvar_name f

  let is_global f = (F.show f).[0] = '.'
  let of_global f =
    let s = F.show f in
    F.from_string @@ String.sub s 1 (String.length s - 1)

  let is_discard f =
    F.(equal f dummyname) ||
    let c = (F.show f).[0] in
      c = '_'

  let is_macro_name f =
      let c = (F.show f).[0] in
      c = '@'

  (* 
    replaces 
    - TArr (t1,t2) with t2 = prop with TPred (o:t1),
    - TArr (t1,t2) with t2 = TPred l with TPred (o:t1, l)
  *)
  let flatten_arrows =
    let rec is_pred = function 
      | Ast.TypeExpression.TConst a -> F.show a = "prop"
      | TArr(_,r) -> is_pred r.tit
      | TApp (_, _, _) | TPred (_, _) -> false
    in
    let rec flatten tloc = function
      | Ast.TypeExpression.TArr (l,r) -> (Ast.Mode.Output, l) :: flatten_loc r 
      | TConst c when F.equal c F.propf -> [] 
      | tit -> [Output,{tit;tloc}]
    and flatten_loc {tit;tloc} = flatten tloc tit
    and main = function
      | Ast.TypeExpression.TPred (b, l) -> 
          Ast.TypeExpression.TPred (b, List.map (fun (a, b) -> a, main_loc b) l)
      | TConst _ as t -> t
      | TApp (n, x, xs) -> TApp (n, main_loc x, List.map main_loc xs)
      | TArr (l, r) when is_pred r.tit -> TPred (Ast.Structured.Relation, (Output, main_loc l) :: flatten_loc r)
      | TArr (l, r) -> TArr(main_loc l, main_loc r)
    and main_loc {tit;tloc} = {tit=main tit;tloc}
    in main_loc

  let rec scope_tye ctx ~loc t : ScopedTypeExpression.t_ =
    match t with
    | Ast.TypeExpression.TConst c when F.show c = "prop" -> Pred (Relation,[])
    | TConst c when F.show c = "any" -> Any
    | TConst c when F.Set.mem c ctx -> Const(Bound elpi_language,c)
    | TConst c -> Const(Scope.mkGlobal (),c)
    | TApp(c,x,[y]) when F.show c = "variadic" ->
        Arrow(Variadic,scope_loc_tye ctx x,scope_loc_tye ctx y)
    | TApp(c,x,xs) ->
        if F.Set.mem c ctx || is_uvar_name c then error ~loc "type schema parameters cannot be type formers";
        App(c,scope_loc_tye ctx x, List.map (scope_loc_tye ctx) xs)
    | TPred(m,xs) -> Pred(m,List.map (fun (m,t) -> m, scope_loc_tye ctx t) xs)
    | TArr(s,t) -> Arrow(NotVariadic, scope_loc_tye ctx s, scope_loc_tye ctx t)
  and scope_loc_tye ctx { tloc; tit } = { loc = tloc; it = scope_tye ctx ~loc:tloc tit }
  let scope_loc_tye ctx (t: Ast.Structured.functionality Ast.TypeExpression.t) =
    scope_loc_tye ctx @@ flatten_arrows t

  let compile_type { Ast.Type.name; loc; attributes; ty } =
    let open ScopedTypeExpression in
    let value = scope_loc_tye F.Set.empty ty in
    let vars =
      let rec aux e { it } =
        match it with
        | App(_,x,xs) -> List.fold_left aux e (x :: xs)
        | Const(Bound _, _) -> assert false (* there are no binders yet *)
        | Const(Global _,c) when is_uvar_name c -> F.Set.add c e
        | Const(Global _,_) -> e
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

  let rec scope_term ~state ctx ~loc t =
    let open Ast.Term in
    match t with
    | Const c when is_discard c -> ScopedTerm.Discard
    | Const c when is_macro_name c ->
        let { macros } = get_mtm state in
        if F.Map.mem c macros then
          ScopedTerm.unlock @@ fst @@ F.Map.find c macros
        else error ~loc (Format.asprintf "@[<hv>Unknown macro %a.@]" F.pp c)
    | Const c when F.Set.mem c ctx -> ScopedTerm.(Const(Bound elpi_language,c))
    | Const c ->
        if is_uvar_name c then ScopedTerm.Var(c,[])
        else if CustomFunctorCompilation.is_singlequote c then CustomFunctorCompilation.scope_singlequote ~loc state c
        else if CustomFunctorCompilation.is_backtick c then CustomFunctorCompilation.scope_backtick ~loc state c
        else if is_global c then ScopedTerm.(Const(Scope.mkGlobal (),of_global c))
        else ScopedTerm.(Const(Scope.mkGlobal (),c))
    | App ({ it = App (f,l1) },l2) -> scope_term ~state ctx ~loc (App(f, l1 @ l2))
    | App({ it = Const c }, [x]) when F.equal c F.spillf ->
        ScopedTerm.Spill (scope_loc_term ~state ctx x,ref ScopedTerm.NoInfo)
    | App({ it = Const c }, l) when F.equal c F.implf || F.equal c F.rimplf ->
        begin match l with 
        | [t1;t2] -> Impl (F.equal c F.implf, scope_loc_term ~state ctx t1, scope_loc_term ~state ctx t2)
        | _ -> error ~loc "implication is a binary operator"
        end
    | App({ it = Const c }, x :: xs) ->
         if is_discard c then error ~loc "Applied discard";
         let x = scope_loc_term ~state ctx x in
         let xs = List.map (scope_loc_term ~state ctx) xs in
         if is_macro_name c then
           let { macros } = get_mtm state in
           if F.Map.mem c macros then ScopedTerm.beta (fst @@ F.Map.find c macros) (x::xs)
           else error ~loc (Format.asprintf "@[<hv>Unknown macro %a.@ Known macros: %a@]" F.pp c (pplist F.pp ", ") (F.Map.bindings macros|>List.map fst))
         else
          let bound = F.Set.mem c ctx in
          if bound then ScopedTerm.App(Bound elpi_language, c, x, xs)
          else if is_uvar_name c then ScopedTerm.Var(c,x :: xs)
          else if is_global c then ScopedTerm.App(Scope.mkGlobal ~escape_ns:true (),of_global c,x,xs)
          else ScopedTerm.App(Scope.mkGlobal (), c, x, xs)
    | Cast (t,ty) ->
        let t = scope_loc_term ~state ctx t in
        let ty = scope_loc_tye F.Set.empty (RecoverStructure.structure_type_expression ty.Ast.TypeExpression.tloc Ast.Structured.Relation (function [] -> Some Ast.Structured.Relation | _ -> None) ty) in
        ScopedTerm.Cast(t,ty)
    | Lam (c,ty,b) when is_discard c ->
        let ty = ty |> Option.map (fun ty -> scope_loc_tye F.Set.empty (RecoverStructure.structure_type_expression ty.Ast.TypeExpression.tloc Ast.Structured.Relation (function [] -> Some Ast.Structured.Relation | _ -> None) ty)) in
        ScopedTerm.Lam (None,ty,scope_loc_term ~state ctx b)
    | Lam (c,ty,b) ->
        if has_dot c then error ~loc "Bound variables cannot contain the namespaec separator '.'";
        let ty = ty |> Option.map (fun ty -> scope_loc_tye F.Set.empty (RecoverStructure.structure_type_expression ty.Ast.TypeExpression.tloc Ast.Structured.Relation (function [] -> Some Ast.Structured.Relation | _ -> None) ty)) in
        ScopedTerm.Lam (Some (c,elpi_language),ty,scope_loc_term ~state (F.Set.add c ctx) b)
    | CData c -> ScopedTerm.CData c (* CData.hcons *)
    | App ({ it = Const _},[]) -> anomaly "Application node with no arguments"
    | App ({ it = Lam _},_) ->
      error ~loc "Beta-redexes not allowed, use something like (F = x\\x, F a)"
    | App ({ it = CData _},_) ->
      error ~loc "Applied literal"
    | App ({ it = Quoted _},_) ->
      error ~loc "Applied quotation"
    | App({ it = Cast _},_) ->
      error ~loc "Casted app not supported yet"
    | Quoted _ -> assert false
  and scope_loc_term ~state ctx { Ast.Term.it; loc } =
    match it with
    | Quoted { Ast.Term.data; kind; qloc } ->
      let unquote =
        match kind with
        | None ->
            let default_quotation = State.get default_quotation state in
            if Option.is_none default_quotation then
              anomaly ~loc "No default quotation";
            option_get default_quotation ~language:"default"
        | Some name ->
            let named_quotations = State.get named_quotations state in
            try StrMap.find name named_quotations ~language:name
            with Not_found -> anomaly ~loc ("No '"^name^"' quotation") in
      let state = update_mtm state (fun x -> { x with ctx }) in
      let simple_t =
        try unquote state qloc data
        with Elpi_parser.Parser_config.ParseError(loc,msg) -> error ~loc msg in
      ScopedTerm.of_simple_term_loc simple_t
    | _ ->
      let it = scope_term ~state ctx ~loc it in
      { ScopedTerm.it; loc; ty = MutableOnce.make (F.from_string "Ty") }

  let scope_loc_term ~state =
    let { ctx } = get_mtm state in
    scope_loc_term ~state ctx

  let scope_type_abbrev { Ast.TypeAbbreviation.name; value; nparams; loc } =
    let rec aux ctx = function
      | Ast.TypeAbbreviation.Lam(c,loc,t) when is_uvar_name c ->
          if F.Set.mem c ctx then error ~loc "duplicate type schema variable";
          ScopedTypeExpression.Lam(c,aux (F.Set.add c ctx) t)
      | Ast.TypeAbbreviation.Lam(c,loc,_) -> error ~loc "only variables can be abstracted in type schema"
      | Ast.TypeAbbreviation.Ty t -> ScopedTypeExpression.Ty (scope_loc_tye ctx t)
  in
    { ScopedTypeExpression.name; value = aux F.Set.empty value; nparams; loc; indexing = None }

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
      | Const(Global _,c) | App(Global _,c,_,_) -> F.Set.add c s
      | Impl(false,{ it = (Const(Global _,c) | App(Global _,c,_,_)) }, _) -> F.Set.add c s
      (* | (Const _ | App _) -> s *)
      | _ -> assert false)
      F.Set.empty cl

  (* let rec append_body b1 b2 =
    match b1, b2 with
    | [], _ -> b2
    | [Scoped.Clauses c1], Scoped.Clauses c2 :: more ->
      Scoped.Clauses (c1 @ c2) :: more
    | x :: xs, _ -> x :: append_body xs b2 *)

  
  let compile_clause state macros { Ast.Clause.body; attributes; loc } =
     let state = set_mtm state { empty_mtm with macros } in
      { Ast.Clause.body = scope_loc_term ~state body; attributes; loc }


  let compile_sequent state macros { Ast.Chr.eigen; context; conclusion } =
     let state = set_mtm state { empty_mtm with macros } in
     { Ast.Chr.eigen = scope_loc_term ~state eigen; context = scope_loc_term ~state context; conclusion = scope_loc_term ~state conclusion }

  let compile_chr_rule state macros { Ast.Chr.to_match; to_remove; guard; new_goal; attributes; loc } =
    let to_match = List.map (compile_sequent state macros) to_match in
    let to_remove = List.map (compile_sequent state macros) to_remove in
    let guard = Option.map (scope_loc_term ~state:(set_mtm state { empty_mtm with macros })) guard in
    let new_goal = Option.map (compile_sequent state macros) new_goal in
    { Ast.Chr.to_match; to_remove; guard; new_goal; attributes; loc }

  let compile_kind kinds { Ast.Type.name; ty; loc } =
    let open Ast.TypeExpression in
    let rec count = function
      | TArr({ tit = TConst c },t) when c == F.typef -> 1 + count t.tit
      | TConst c when c == F.typef -> 0
      | x -> error ~loc "Syntax error: illformed kind.\nExamples:\nkind bool type.\nkind list type -> type.\n"
    in
    F.Map.add name (count ty.tit, loc) kinds  
    
  let compile_macro state m { Ast.Macro.loc; name; body } =
    try
      let _, oloc = F.Map.find name m in
      error ~loc (Format.asprintf "duplicate macro %a, previous declaration %a" F.pp name Loc.pp oloc)
    with Not_found ->
      let body = scope_loc_term ~state:(set_mtm state { empty_mtm with macros = m }) body in
      F.Map.add name (body,loc) m

  let run state ~toplevel_macros p : State.t * Scoped.program =

    let rec compile_program omacros state { Ast.Structured.macros; kinds; types; type_abbrevs; modes; body } =
      let active_macros = List.fold_left (compile_macro state) omacros macros in
      let type_abbrevs = List.map compile_type_abbrev type_abbrevs in
      let kinds = List.fold_left compile_kind F.Map.empty kinds in
      let types = List.fold_left (fun m t -> map_append t.Ast.Type.name (TypeList.make @@ compile_type t) m) F.Map.empty (List.rev types) in
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
          let compiled_cl = List.map (compile_clause state macros) cl in
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
          let rules = List.map (compile_chr_rule state macros) rules in
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
    let state, toplevel_macros, pbody = compile_program toplevel_macros state p in
    (* Printf.eprintf "run: %d\n%!" (F.Map.cardinal toplevel_macros); *)
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
    TypeAssignment.overloaded_skema_with_id F.Map.t ->
    TypeAssignment.overloaded_skema_with_id F.Map.t ->
    TypeAssignment.overloaded_skema_with_id F.Map.t
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
      | Impl(b,t1,t2) -> 
          let t1' = aux_loc t1 in
          let t2' = aux_loc t2 in
          if t1 == t1' && t2 == t2' then it
          else Impl(b,t1',t2')
      | Const((Bound _|Global { escape_ns = true }),_) -> it
      | Const(Global { escape_ns = false },c) -> let c' = f c in if c == c' then it else Const(Scope.mkGlobal (),c')
      | Spill(t,n) -> let t' = aux_loc t in if t' == t then it else Spill(t',n)
      | App(scope,c,x,xs) ->
          let c' = if scope = Scope.mkGlobal () then f c else c in
          let x' = aux_loc x in
          let xs' = smart_map aux_loc xs in
          if c == c' && x == x' && xs == xs' then it
          else App(scope,c',x',xs')
      | Lam(n,ty,b) ->
          let b' = aux_loc b in
          let ty' = option_smart_map (ScopedTypeExpression.smart_map_scoped_loc_ty f) ty in
          if b == b' && ty' == ty then it else Lam(n,ty',b')
      | Var(c,l) ->
          let l' = smart_map aux_loc l in
          if l == l' then it else Var(c,l')
      | Cast(t,ty) ->
          let t' = aux_loc t in
          let ty' = ScopedTypeExpression.smart_map_scoped_loc_ty f ty in
          if t' == t && ty' == ty then it else Cast(t',ty')
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
      (* We give precedence to recent type declarations over old ones *)
      F.Map.union (fun f l1 l2 ->
        Some (TypeAssignment.merge_skema l2 l1)) t1 t2

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

    let merge_type_abbrevs m1 m2 = m1 @ m2

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

module Check : sig

  val check : State.t -> base:Assembled.program -> unchecked_compilation_unit -> checked_compilation_unit

end = struct

  let check st ~base u : checked_compilation_unit =
    let { Assembled.symbols; prolog_program; indexing; 
      modes = om; functional_preds = ofp; kinds = ok; types = ot; type_abbrevs = ota; 
      chr = ochr; toplevel_macros = otlm; total_type_checking_time; types_ids = otyid } = base in
    let { version; code = { Flat.toplevel_macros; kinds; types; type_abbrevs; modes; clauses; chr; builtins }} = u in

    let all_kinds = Flatten.merge_kinds ok kinds in

    (* Functionality *)
    let check_func_begin = Unix.gettimeofday () in
    let functional_preds = 
      FunctionalityChecker.merge_types_and_abbrevs ~old:F.Map.empty ~types ~type_abbrevs in
    let all_functional_preds = FunctionalityChecker.merge ofp functional_preds in
    let check_func_end = Unix.gettimeofday () in

    let all_ty_id = ref otyid in (* TODO: this should be taken into account... *)
    let add_all_ty_id k v = all_ty_id := C.Map.add k v !all_ty_id in

    let local_ty_id = ref C.Map.empty in
    let add_local_ty_id k v = all_ty_id := C.Map.add k v !local_ty_id in

    (* Typeabbreviation *)
    let check_k_begin = Unix.gettimeofday () in
    let all_type_abbrevs, type_abbrevs =
      List.fold_left (fun (all_type_abbrevs,type_abbrevs) (name, ty) ->
        (* TODO check disjoint from kinds *)
        let loc = ty.ScopedTypeExpression.loc in
        let id, ty = TypeChecker.check_type ~type_abbrevs:all_type_abbrevs ~kinds:all_kinds ty in
        if F.Map.mem name all_type_abbrevs then begin
          let (_,sk), otherloc = F.Map.find name all_type_abbrevs in
          if TypeAssignment.compare_skema sk ty <> 0 then
          error ~loc
            ("Duplicate type abbreviation for " ^ F.show name ^
              ". Previous declaration: " ^ Loc.show otherloc)
        end;
        add_all_ty_id id ty;
        add_local_ty_id id ty;
        F.Map.add name ((id, ty),loc) all_type_abbrevs, F.Map.add name ((id,ty),loc) type_abbrevs)
        (ota,F.Map.empty) type_abbrevs in
    let check_k_end = Unix.gettimeofday () in

    (* Type checking *)
    let check_t_begin = Unix.gettimeofday () in
    (* TypeChecker.check_disjoint ~type_abbrevs ~kinds; *)
    let types_indexing = F.Map.map (List.map (fun ty -> ty.ScopedTypeExpression.indexing, ty.ScopedTypeExpression.loc)) types in
    let types = F.Map.map (fun e -> 
      let tys = TypeChecker.check_types ~type_abbrevs:all_type_abbrevs ~kinds:all_kinds e in
      TypeAssignment.iter_overloading (fun (a,b) -> add_all_ty_id a b) tys;
      tys) types in
    let check_t_end = Unix.gettimeofday () in

    let all_types = Flatten.merge_type_assignments ot types in

    let check_begin = Unix.gettimeofday () in

    Format.printf "Functional pred are %a\n%!" FunctionalityChecker.pp functional_preds;

    (* let xxx = open_out "/home/dfissore/Documents/github/ELPI_DEV/unique-id/log" in *)
    (* Util.set_spaghetti_printer pp_const Format.pp_print_int; *)
    (* Format.fprintf (Format.formatter_of_out_channel xxx) "%a@." (C.Map.pp TypeAssignment.pp_skema) !all_ty_id; *)

    let clauses = clauses |> List.map (fun ({ Ast.Clause.body; loc; attributes = { Ast.Structured.typecheck } } as c) ->
      if typecheck then
        let needs_spill = TypeChecker.check ~type_abbrevs:all_type_abbrevs ~kinds:all_kinds ~types:all_types body ~exp:(Val Prop) in
        (* Format.fprintf (Format.formatter_of_out_channel xxx) "%a\n" ScopedTerm.pp body; *)
        FunctionalityChecker.check_clause ~loc ~functional_preds body;
        needs_spill, c
      else
        false, c) in
    let check_end = Unix.gettimeofday () in
      (* close_out xxx; *)
    let checked_code = { CheckedFlat.toplevel_macros; kinds; types; types_indexing; type_abbrevs; modes; clauses; chr; builtins; functional_preds; types_ids = !local_ty_id } in


  { version; checked_code; base_hash = hash_base base;
    precomputed_kinds =all_kinds;
    precomputed_type_abbrevs = all_type_abbrevs;
    precomputed_types = all_types;
    precomputed_types_ids = !all_ty_id;
    precomputed_functional_preds = all_functional_preds;
    type_checking_time = check_end -. check_begin +. check_t_end -. check_t_begin +. check_k_end -. check_k_begin +. check_func_end -. check_func_begin }

end


let todopp name _fmt _ = error ("pp not implemented for field: "^name)

let get_argmap, set_argmap, _update_argmap, drop_argmap =
  let argmap =
    State.declare
      ~name:"elpi:argmap" ~pp:(todopp "elpi:argmap")
      ~descriptor:D.elpi_state_descriptor
      ~clause_compilation_is_over:(fun _ -> F.Map.empty)
      ~goal_compilation_begins:(fun x -> x)
      ~goal_compilation_is_over:(fun ~args:_ _ -> None)
      ~compilation_is_over:(fun _ -> None)
      ~execution_is_over:(fun _ -> None)
     ~init:(fun () -> F.Map.empty) in
  State.(get argmap, set argmap, update_return argmap, drop argmap)

  let is_Arg state x = 
    match x with
    | Arg _ | AppArg _ -> true
    | _ -> false
  
  let mk_Arg state ~name ~args =
    let name = F.from_string name in
    let state, i =
      let amap = get_argmap state in
      try state, F.Map.find name amap
      with Not_found ->
        let i = F.Map.cardinal amap in
        let amap = F.Map.add name i amap in
        set_argmap state amap, i in
    match args with
    | [] -> state, mkArg i 0
    | xs -> state, mkAppArg i xs
  
  let get_Arg state ~name ~args =
    let name = F.from_string name in
    let amap = get_argmap state in
    let i =
      try F.Map.find name amap
      with Not_found -> error "get_Arg" in
    match args with
    | [] -> mkArg i 0
    | xs -> mkAppArg i xs
  
  let fresh_Arg =
    let qargno = ref 0 in
    fun state ~name_hint:name ~args ->
      incr qargno;
      let name = Printf.sprintf "%s_%d_" name !qargno in
      mk_Arg state ~name ~args

module Assemble : sig

  val extend : flags -> State.t -> Assembled.program -> checked_compilation_unit -> State.t * Assembled.program

  (* for the query *)
  val compile_query : State.t -> Assembled.program -> bool * ScopedTerm.t -> SymbolMap.table * int F.Map.t * D.term
  val compile_query_term : State.t -> Assembled.program -> depth:int -> ScopedTerm.t -> State.t * D.term

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

    (* THE MISTERY: allocating symbols following their declaration order makes the grundlagen job 30% faster (600M less memory):
            time   typchk wall   mem
      with: 14.75   0.53  16.69 2348.4M
      wout: 19.61   0.56  21.72 2789.1M 
    *)
    let symbols =
      if F.Map.cardinal types > 2000 then
        F.Map.bindings types |> List.map (fun (k,l) -> k,snd (List.hd l)) |> List.sort (fun (_,l1) (_,l2) -> compare l1.Loc.line l2.Loc.line) |> List.map fst |> List.fold_left (fun s k -> fst @@ SymbolMap.allocate_global_symbol state s k) symbols
      else
        symbols in

    let symbols, map =
      F.Map.fold (fun tname l (symbols, acc) ->
        let symbols, (c,_) = SymbolMap.allocate_global_symbol state symbols tname in
        symbols, TypeList.fold (fun acc (indexing, loc) ->
                   add_indexing_for ~loc tname c indexing acc)
                  acc l)
      types (symbols, C.Map.empty) in
    let symbols, map =
      F.Map.fold (fun k (_,loc) (symbols,m) ->
        let symbols, (c,_) = SymbolMap.allocate_global_symbol state symbols k in
        symbols, add_indexing_for ~loc k c None m) modes (symbols, map) in
    symbols, R.CompileTime.update_indexing map index, C.Map.union (fun _ _ _ -> assert false) map old_idx

  type spill = { vars : ScopedTerm.t list; vars_names : F.t list; expr : ScopedTerm.t }
  type spills = spill list

  let todbl ~needs_spilling state symb ?(depth=0) ?(amap = F.Map.empty) t =
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
    let lookup_bound loc (_,ctx) (c,l as x) =
      try Scope.Map.find x ctx
      with Not_found -> error ~loc ("Unbound variable " ^ F.show c ^ if l <> elpi_language then " (language: "^l^")" else "") in
    let allocate_bound_symbol loc ctx f =
      let c = lookup_bound loc ctx f in
      let s, rc = SymbolMap.allocate_bound_symbol state !symb c in
      symb := s;
      rc in
    let push_bound (n,ctx) c = (n+1,Scope.Map.add c n ctx) in
    let push_unnamed_bound (n,ctx) = (n+1,ctx) in
    let push ctx = function
      | None -> push_unnamed_bound ctx
      | Some x -> push_bound ctx x in
    let open ScopedTerm in
    let rec todbl (ctx : int * _ Scope.Map.t) t =
      match t.it with
      | Impl(b,t1,t2) ->
          D.mkApp (D.Global_symbols.(if b then implc else rimplc)) (todbl ctx t1) [todbl ctx t2]
      | CData c -> D.mkCData (CData.hcons c)
      | Spill(t,_) -> assert false (* spill handled before *)
      | Cast(t,_) -> todbl ctx t
      (* lists *)
      | Const(Global _,c) when F.(equal c nilf) -> D.mkNil
      | App(Global _,c,x,[y]) when F.(equal c consf) ->
          let x = todbl ctx x in
          let y = todbl ctx y in
          D.mkCons x y
      (* globals and builtins *)
      | Const(Global _,c) ->
          let c, t = allocate_global_symbol c in
          if Builtins.is_declared state c then D.mkBuiltin c []
          else t
      | App(Global _,c,x,xs) ->
          let c,_ = allocate_global_symbol c in
          let x = todbl ctx x in
          let xs = List.map (todbl ctx) xs in
          if Builtins.is_declared state c then D.mkBuiltin c (x::xs)
          else D.mkApp c x xs
      (* lambda terms *)
      | Const(Bound l,c) -> allocate_bound_symbol t.loc ctx (c,l)
      | Lam(c,_,t) -> D.mkLam @@ todbl (push ctx c) t
      | App(Bound l,c,x,xs) ->
          let c = lookup_bound t.loc ctx (c,l) in
          let x = todbl ctx x in
          let xs = List.map (todbl ctx) xs in
          D.mkApp c x xs
      (* holes *)
      | Var(c,xs) ->
          let xs = List.map (todbl ctx) xs in
          R.mkAppArg (allocate_arg c) 0 xs
      | Discard -> D.mkDiscard
    in

    let is_prop ~extra x =
      let ty = TypeAssignment.deref x in
      let rec aux extra = function
          | TypeAssignment.Prop -> true
          | TypeAssignment.Arr(_,_,t) when extra > 0 -> aux (extra-1) t
          | TypeAssignment.UVar r when MutableOnce.is_set r -> aux extra (TypeAssignment.deref r)
          | _ -> false in
      aux extra ty in

    let mk_loc ~loc ?(ty = MutableOnce.make (F.from_string "Spill")) it = { ty; it; loc } in (* TODO store the types in Main *)

    (* let sigma ~loc t n =
      mk_loc ~loc @@ App(Global,F.sigmaf,mk_loc ~loc (Lam(Some n, t)),[]) in *)

    let add_spilled l t =
      if l = [] then t
      else
        let t =
          (* Format.eprintf "adding %d spills\n" (List.length l); *)
          List.fold_right (fun { expr; vars_names } t ->
            let t = mk_loc ~loc:t.loc @@ App(Scope.mkGlobal ~escape_ns:true (),F.andf,expr,[t]) in
             (* let t = List.fold_left (sigma ~loc:t.loc) t vars_names in *)
             t
             ) l t in
        t
    in

    let mkApp g c l =
      if l = [] then Const(g,c)
      else App(g,c,List.hd l,List.tl l) in

    (* let rec apply_to locals w ({ it; loc; ty } as orig) =
      match it with
      | App(g,c,x,xs) ->
        mk_loc ~loc ~ty @@ mkApp g c (List.map (apply_to locals w) (x::xs))
      | Var(c,xs) when List.mem c locals -> mk_loc ~loc ~ty @@ Var(c,w :: xs)
      | Lam(c,o,t) -> mk_loc ~loc ~ty @@ Lam(c,o,apply_to locals w t)
      | Const _ | Discard | Var _ | CData _ -> orig
      | Cast (t,i) -> mk_loc ~loc ~ty @@ Cast(apply_to locals w t,i)
      | Impl(b,t1,t2) -> mk_loc ~loc ~ty @@ Impl(b, apply_to locals w t1, apply_to locals w t2)
      | Spill _ -> assert false in
    let apply_to locals (w,l) t =
      let w = mk_loc ~loc:t.loc @@ Const(Bound l,w) in
      apply_to locals w t in *)

    let app t args =
      if args = [] then t else
      let rec aux { loc; it; ty } : t =
        mk_loc ~loc ~ty @@
          match it with
          | App(Global _ as g,c,x,xs) when F.equal c F.andf ->
              mkApp g c (aux_last (x::xs))
          | Impl(b,s,t) -> Impl(b,s,aux t)
          | Const(g,c) -> mkApp g c args
          | App(g,c,x,xs) -> mkApp g c (x :: xs @ args)
          | Var _
          | Discard | Lam (_, _, _)
          | CData _ | Spill (_, _) | Cast (_, _) -> assert false
      and aux_last = function
        | [] -> assert false
        | [x] -> [aux x]
        | x :: xs -> x :: aux_last xs
      in
        aux t in

    let args = ref 0 in

    let rec mk_spilled ~loc ctx n =
      if n = 0 then []
      else
        let f = incr args; F.from_string (Printf.sprintf "%%arg%d" !args) in
        let sp = mk_loc ~loc @@ Var(f,ctx) in
        (f,sp) :: mk_spilled ~loc ctx (n-1) in

    (* barendregt_convention (naive implementation) *)
    let rec bc ctx t =
      match t with
      | Lam(None,o,t) -> Lam(None,o,bc_loc ctx t)
      | Lam(Some (c,l),o,t) when List.mem (c,l) ctx ->
        let d = fresh () in
        bc ctx (Lam(Some (d,l),o,rename_loc l c d t))
      | Lam(Some c,o,t) -> Lam (Some c,o, bc_loc (c :: ctx) t)
      | Impl(b,t1,t2) -> Impl(b,bc_loc ctx t1, bc_loc ctx t2)
      | Cast(t,ty) -> Cast(bc_loc ctx t,ty)
      | Spill(t,i) -> Spill(bc_loc ctx t,i)
      | App(g,f,x,xs) -> App(g,f,bc_loc ctx x,List.map (bc_loc ctx) xs)
      | Const _ | Discard | Var _ | CData _ -> t
    and bc_loc ctx { loc; ty; it } =
      { loc; ty; it = bc ctx it }
    in

    let rec spill ?(extra=0) ctx ({ loc; ty; it } as t) : spills * ScopedTerm.t list =
      (* Format.eprintf "@[<hov 2>spill %a :@ %a@]\n" ScopedTerm.pretty t TypeAssignment.pretty (TypeAssignment.deref ty); *)
      match it with
      | CData _ | Discard | Const _ -> [],[t]
      | Cast(t,_) -> spill ctx t
      | Spill(t,{ contents = NoInfo}) -> assert false (* no type checking *)
      | Spill(t,{ contents = (Phantom _)}) -> assert false (* escapes type checker *)
      | Spill(t,{ contents = (Main n)}) ->
          let vars_names, vars = List.split @@ mk_spilled ~loc (List.rev_map (fun (c,l) -> mk_loc ~loc @@ Const(Bound l,c)) ctx) n in
          let spills, t = spill1 ~extra:(List.length vars_names) ctx t in
          let expr = app t vars in
          spills @ [{vars; vars_names; expr}], vars
      (* globals and builtins *)
      | App(Global _ as f,c,{ it = Lam(Some v,o,t); loc = tloc; ty = tty },[]) when F.equal F.pif c ->
          let ctx = v :: ctx in
          let spilled, t = spill1 ctx t in
          [], [{loc;ty;it = App(f,c,{ it = Lam(Some v,o,add_spilled spilled t); loc = tloc; ty = tty },[])}]
      | App(Global _ as f,c,{ it = Lam(Some v,o,t); loc = tloc; ty = tty },[]) when F.equal F.sigmaf c ->
            let ctx = ctx in (* not to be put in scope of spills *)
            let spilled, t = spill1 ctx t in
            [], [{loc;ty;it = App(f,c,{ it = Lam(Some v,o,add_spilled spilled t); loc = tloc; ty = tty },[])}]
      | App(g,c,x,xs) ->
          let last = if F.equal F.andf c then List.length xs else -1 in
          let spills, args = List.split @@ List.mapi (fun i -> spill ~extra:(if i = last then extra else 0) ctx) (x :: xs) in
          let args = List.flatten args in
          let spilled = List.flatten spills in
          let it = App(g,c,List.hd args, List.tl args) in
          let extra = extra + List.length args - List.length xs - 1 in
          (* Format.eprintf "%a\nspill %b %d %a : %a\n" Loc.pp loc (is_prop ~extra ty) extra F.pp c TypeAssignment.pretty (TypeAssignment.UVar ty); *)
          if is_prop ~extra ty then [], [add_spilled spilled { it; loc; ty }]
          else spilled, [{ it; loc; ty }]

      (* TODO: positive/negative postion, for now we assume :- and => are used in the obvious way *)
      | Impl(false,head,premise) -> (* head :- premise *)
          let spills_head, head = spill1 ctx head in
          if spills_head <> [] then error ~loc "Spilling in the head of a clause is not supported";
          let spilled, premise = spill1 ctx premise in
          let it = Impl(false,head,premise) in
          [],[add_spilled spilled { it; loc; ty }]
      | Impl(true,premise,conclusion) -> (* premise => conclusion *)
          let spills_premise, premise = spill1 ctx premise in
          if spills_premise <> [] then error ~loc "Spilling in the premise of an implication is not supported";
          let spilled, conclusion = spill1 ~extra ctx conclusion in
          let it = Impl(true,premise,conclusion) in
          [], [add_spilled spilled { it; loc; ty }]
      (* lambda terms *)
      | Lam(None,o,t) ->
          let spills, t = spill1 ctx t in
          spills, [{ it = Lam(None,o,t); loc; ty }]
      | Lam(Some c,o,t) ->
          let spills, t = spill1 (c::ctx) t in
          let (t,_), spills =
            map_acc (fun (t,n) { vars; vars_names; expr } ->
              let all_names = vars_names @ n in
              (t,all_names), { vars; vars_names; expr = mk_loc ~loc @@ App(Scope.mkGlobal ~escape_ns:true (),F.pif,mk_loc ~loc @@ Lam(Some c,o,expr),[]) })
            (t,[]) spills in
          spills, [{ it = Lam(Some c,o,t); loc; ty }]
      (* holes *)
      | Var(c,xs) ->
          let spills, args = List.split @@ List.map (spill ctx) xs in
          let args = List.flatten args in
          let spilled = List.flatten spills in
          let it = Var(c,args) in
          let extra = extra + List.length args - List.length xs in
          if is_prop ~extra ty then [], [add_spilled spilled { it; loc; ty }]
          else spilled, [{ it; loc; ty }]
      and spill1 ?extra ctx ({ loc } as t) =
        let spills, t = spill ?extra ctx t in
        let t = if List.length t <> 1 then error ~loc "bad pilling" else List.hd t in
        spills, t
  in
  let spill ctx t =
    (* Format.eprintf "before spill: %a\n" ScopedTerm.pretty t; *)
    let s,t = spill ctx t in
    (* Format.eprintf "after spill: %a\n" ScopedTerm.pretty (List.hd t); *)

    s,t
in

    let spills, ts =
      if needs_spilling then spill [] (bc_loc [] t)
      else [],[t] in
    let t =
      match spills, ts with
      | [], [t] -> t
      | [], _ -> assert false
      | _ :: _, _ -> error ~loc:t.loc "Cannot place spilled expression" in
    (* if needs_spilling then Format.eprintf "spilled %a\n" ScopedTerm.pretty t; *)
    let t  = todbl (depth,Scope.Map.empty) t in
    (!symb, !amap), t  

  let extend1_clause flags state modes indexing (clauses,symbols, index) (needs_spilling,{ Ast.Clause.body; loc; attributes = { Ast.Structured.insertion = graft; id; ifexpr } }) =
    if not @@ filter1_if flags (fun x -> x) ifexpr then
      (clauses,symbols, index)
    else
    let (symbols, amap), body = todbl ~needs_spilling state symbols body in
    let modes x = try fst @@ F.Map.find (SymbolMap.global_name state symbols x) modes with Not_found -> [] in
    let (p,cl), _, morelcs =
      try R.CompileTime.clausify1 ~loc ~modes ~nargs:(F.Map.cardinal amap) ~depth:0 body
      with D.CannotDeclareClauseForBuiltin(loc,c) ->
        error ?loc ("Declaring a clause for built in predicate " ^ F.show @@ SymbolMap.global_name state symbols c)
      in
    if morelcs <> 0 then error ~loc "sigma in a toplevel clause is not supported";
    let index = R.CompileTime.add_to_index ~depth:0 ~predicate:p ~graft cl id index in
    (graft,id,p,cl) :: clauses, symbols, index


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
    let todbl state (symbols,amap) t = todbl ~needs_spilling:false (* TODO typecheck *) state symbols ~amap t in
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
    (state, { Assembled.hash; clauses = cl; symbols; prolog_program; indexing; modes = om; kinds = ok; functional_preds = ofp; types = ot; type_abbrevs = ota; chr = ochr; toplevel_macros = otlm; total_type_checking_time; types_ids = otyid })
            { version; base_hash; checked_code = { CheckedFlat.toplevel_macros; kinds; types; types_ids; types_indexing; type_abbrevs; modes; functional_preds; clauses; chr; builtins}; precomputed_kinds; precomputed_type_abbrevs; precomputed_functional_preds; precomputed_types; type_checking_time; } =
    let symbols, prolog_program, indexing = update_indexing state symbols prolog_program modes types_indexing indexing in
    let kinds, type_abbrevs, types, functional_preds, types_ids =
      if hash = base_hash then
        precomputed_kinds, precomputed_type_abbrevs, precomputed_types, precomputed_functional_preds, types_ids
      else
        let kinds = Flatten.merge_kinds ok kinds in
        let type_abbrevs = merge_type_abbrevs ota type_abbrevs in
        let types = Flatten.merge_type_assignments ot types in
        let functional_preds = FunctionalityChecker.merge ofp functional_preds in
        (* TODO: this error message is unclear, maybe we should add the name F.t to the map  *)
        let types_ids = C.Map.union (fun k _ -> error ("Duplicate functionality declaration for " ^ C.show k)) otyid types_ids in
        kinds, type_abbrevs, types, functional_preds, types_ids
    in
    let modes = Flatten.merge_modes om modes in

    let symbols, state =
      List.fold_left (fun (symbols,state) (D.BuiltInPredicate.Pred(name,_,_) as p) ->
        let symbols, (c,_) = SymbolMap.allocate_global_symbol state symbols (F.from_string name) in
        let state = Builtins.register state p c in
        symbols,state) (symbols,state) builtins in
    let total_type_checking_time = total_type_checking_time +. type_checking_time in

    let symbols, chr =
      List.fold_left (extend1_chr_block flags state) (symbols,ochr) chr in
    let clauses, symbols, prolog_program =
      List.fold_left (extend1_clause flags state modes indexing) (cl, symbols, prolog_program) clauses in
  
    (* TODO: @FissoreD here we have to do mutual excl clauses... *)

    let new_base = 
      { Assembled.hash; clauses; symbols; prolog_program; indexing; modes; functional_preds; kinds; types; type_abbrevs; chr; toplevel_macros; total_type_checking_time; types_ids } in
    let hash = hash_base new_base in
    state, { new_base with hash }

  let extend flags state assembled u = extend1 flags (state, assembled) u

  let compile_query state { Assembled.symbols; } (needs_spilling,t) =
    let (symbols, amap), t = todbl ~needs_spilling state symbols t in
    symbols, amap, t 

  let compile_query_term state { Assembled.symbols; } ~depth t =
    let amap = get_argmap state in
    let (symbols', amap), rt = todbl ~needs_spilling:false state symbols ~depth ~amap t in
    if SymbolMap.equal symbols' symbols then set_argmap state amap, rt
    else error ~loc:t.ScopedTerm.loc "cannot allocate new symbols in the query"

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

  let s, p = Scope_Quotation_Macro.run ~toplevel_macros s p in

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
  }
;;

let print_unit { print_units } x =
    if print_units then
      let b1 = Marshal.to_bytes x.code [] in
      Printf.eprintf "== UNIT =================\ncode: %dk (%d clauses)\n\n%!"
        (Bytes.length b1 / 1024) (List.length x.code.Flat.clauses)
;;

let assemble_unit ~flags ~header:(s,base) units : program =

  let s, p = Assemble.extend flags s base units in

  let { print_passes } = flags in

  if print_passes then
    Format.eprintf "== Assembled ================@\n@[<v 0>%a@]@\n"
      Assembled.pp_program p;

 s, p
;;


let header_of_ast ~flags ~parser:p state_descriptor quotation_descriptor hoas_descriptor calc_descriptor builtins ast : header =
  let state = D.State.(init (merge_descriptors D.elpi_state_descriptor state_descriptor)) in
  let state =
    match hoas_descriptor.D.HoasHooks.extra_goals_postprocessing with
    | Some x ->
        D.State.set D.Conversion.extra_goals_postprocessing state x
    | None -> state in
  let { Compiler_data.QuotationHooks.default_quotation;
        named_quotations;
        singlequote_compilation;
        backtick_compilation } = quotation_descriptor in

  let state = D.State.set CustomFunctorCompilation.backtick state backtick_compilation in
  let state = D.State.set CustomFunctorCompilation.singlequote state singlequote_compilation in
  let state = D.State.set Quotation.default_quotation state default_quotation in
  let state = D.State.set Quotation.named_quotations state named_quotations in
  let state =
    let eval_map = List.fold_left (fun m (c,{ CalcHooks.code }) -> Constants.Map.add c code m) Constants.Map.empty (List.rev calc_descriptor) in
    D.State.set CalcHooks.eval state eval_map in
  let state = D.State.set parser state (Some p) in
  let state = D.State.set D.while_compiling state true in
  (* let state = State.set Symbols.table state (Symbols.global_table ()) in *)
  let state, u = unit_or_header_of_ast flags state ast in
  let builtins =
    List.flatten @@
    List.map (fun (_,decl) -> decl |> List.filter_map (function
      | Data.BuiltInPredicate.MLCode (p,_) -> Some p
      | _ -> None)) builtins in
  let u = { u with code = { u.code with builtins }} in (* UGLY *)
  print_unit flags u;
  let u = Check.check state ~base:(Assembled.empty ()) u in
  let init = { (Assembled.empty ()) with toplevel_macros = u.checked_code.toplevel_macros } in
  let h = assemble_unit ~flags ~header:(state,init) u in
  (* Printf.eprintf "header_of_ast: %d\n%!" (F.Map.cardinal (snd h).Assembled.toplevel_macros); *)
  h

let check_unit ~base:(st,base) u = Check.check st ~base u

let empty_base ~header:b = b

let unit_of_ast ~flags ~header:(s, u) p : unchecked_compilation_unit =
  (* Printf.eprintf "unit_of_ast: %d\n%!" (F.Map.cardinal u.Assembled.toplevel_macros); *)
  let _, u = unit_or_header_of_ast flags s ~toplevel_macros:u.Assembled.toplevel_macros p in
  print_unit flags u;
  u

let append_unit ~flags ~base:(s,p) unit : program =
  let s, p = Assemble.extend flags s p unit in
  let { print_passes } = flags in

  if print_passes then
    Format.eprintf "== Assembled ================@\n@[<v 0>%a@]@\n"
     Assembled.pp_program p;

  s, p

let program_of_ast ~flags ~header:((st, base) as header) p : program =
  let u = unit_of_ast ~flags ~header p in
  let u = Check.check st ~base u in
  assemble_unit ~flags ~header u

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
let total_type_checking_time { WithMain.total_type_checking_time = x } = x

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
  let { Assembled.kinds; types; type_abbrevs; toplevel_macros; chr; prolog_program; total_type_checking_time } = assembled_program in
  let total_type_checking_time = assembled_program.Assembled.total_type_checking_time in
  let t = Scope_Quotation_Macro.scope_loc_term ~state:(set_mtm compiler_state { empty_mtm with macros = toplevel_macros }) t in
  let needs_spilling = TypeChecker.check ~type_abbrevs ~kinds ~types t ~exp:TypeAssignment.(Val Prop) in
  let symbols, amap, query = Assemble.compile_query compiler_state assembled_program (needs_spilling,t) in
  let query_env = Array.make (F.Map.cardinal amap) D.dummy in
  let initial_goal = R.move ~argsdepth:0 ~from:0 ~to_:0 query_env query in
  let assignments = F.Map.fold (fun k i m -> StrMap.add (F.show k) query_env.(i) m) amap StrMap.empty in
  {
    WithMain.prolog_program;
    chr;
    symbols;
    query_arguments = Query.N;
    initial_goal;
    assignments;
    compiler_state = compiler_state |> (uvbodies_of_assignments assignments) |> state_update;
    total_type_checking_time;
  }

let term_to_raw_term state (_, assembled_program) ~depth t =
  let { Assembled.kinds; types; type_abbrevs; toplevel_macros = _; chr; prolog_program; total_type_checking_time } = assembled_program in
  let needs_spilling = TypeChecker.check ~type_abbrevs ~kinds ~types t ~exp:(TypeChecker.unknown_type_assignment "Ty") in
  if needs_spilling then
    error "spilling not implemented in term_to_raw_term";
  Assemble.compile_query_term state assembled_program ~depth t


let query_of_scoped_term (compiler_state, assembled_program) f =
  let compiler_state = State.begin_goal_compilation compiler_state in
  let { Assembled.kinds; types; type_abbrevs; toplevel_macros = _; chr; prolog_program; total_type_checking_time } = assembled_program in
  let total_type_checking_time = assembled_program.Assembled.total_type_checking_time in
  let compiler_state,t = f compiler_state in
  let needs_spilling = TypeChecker.check ~type_abbrevs ~kinds ~types t ~exp:TypeAssignment.(Val Prop) in
  let symbols, amap, query = Assemble.compile_query compiler_state assembled_program (needs_spilling,t) in
  let query_env = Array.make (F.Map.cardinal amap) D.dummy in
  let initial_goal = R.move ~argsdepth:0 ~from:0 ~to_:0 query_env query in
  let assignments = F.Map.fold (fun k i m -> StrMap.add (F.show k) query_env.(i) m) amap StrMap.empty in
  {
    WithMain.prolog_program;
    chr;
    symbols;
    query_arguments = Query.N;
    initial_goal;
    assignments;
    compiler_state = compiler_state |> (uvbodies_of_assignments assignments);
    total_type_checking_time;
  }
    
  let query_of_raw_term (compiler_state, assembled_program) f =
    let compiler_state = State.begin_goal_compilation compiler_state in
    let { Assembled.kinds; types; type_abbrevs; toplevel_macros = _; chr; prolog_program; total_type_checking_time } = assembled_program in
    let total_type_checking_time = assembled_program.Assembled.total_type_checking_time in
    let compiler_state, query, gls = f compiler_state in
    let compiler_state, gls = Data.State.get Data.Conversion.extra_goals_postprocessing compiler_state gls compiler_state in
    let gls = List.map Data.Conversion.term_of_extra_goal gls in
    let query =
      match gls @ [query] with
      | [] -> assert false
      | [g] -> g
      | x :: xs -> mkApp D.Global_symbols.andc x xs in
    let amap = get_argmap compiler_state in
    let query_env = Array.make (F.Map.cardinal amap) D.dummy in
    let initial_goal = R.move ~argsdepth:0 ~from:0 ~to_:0 query_env query in
    let assignments = F.Map.fold (fun k i m -> StrMap.add (F.show k) query_env.(i) m) amap StrMap.empty in
    {
      WithMain.prolog_program;
      chr;
      symbols = assembled_program.Assembled.symbols;
      query_arguments = Query.N;
      initial_goal;
      assignments;
      compiler_state = compiler_state |> (uvbodies_of_assignments assignments);
      total_type_checking_time;
    }
  
(* let query_of_data (state, p) loc (Query.Query { arguments } as descr) =
  let query = query_of_term (state, p) (fun ~depth state ->
    let state, term, gls = R.embed_query ~mk_Arg ~depth state descr in
    state, (loc, term), gls) in
  { query with query_arguments = arguments } *)


(* let lookup_query_predicate (state, p) pred =
  let state, pred = Symbols.allocate_global_symbol_str state pred in
  (state, p), pred *)

module Compiler : sig

  val run : 'a query -> 'a executable

end = struct (* {{{ *)


let run
  {
    WithMain.prolog_program;
    chr;
    symbols;
    initial_goal;
    assignments;
    compiler_state = state;
    query_arguments;
  }
=
  (* check_all_builtin_are_typed state types;
  check_no_regular_types_for_builtins state types; *)
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
  List.filter_map (function
    | (Some (Ast.Structured.Remove x),_,_,_) -> Some x
    | (Some (Ast.Structured.Replace x),_,_,_) -> Some x
    | _ -> None) l

let handle_clause_graftin (clauses: (Ast.Structured.insertion option * string option * constant * clause) list) : (string option * constant * clause) list =
  let clauses = clauses |> List.sort (fun (_,_,_,c1) (_,_,_,c2) -> R.lex_insertion c1.timestamp c2.timestamp) in
  let removals = removals clauses in
  let clauses = clauses |> List.filter (fun (_,id,_,_) -> id = None || not(List.exists (fun x -> id = Some x) removals)) in
  let clauses = clauses |> List.filter (fun (c,_,_,_) -> match c with Some (Ast.Structured.Remove _) -> false | _ -> true) in
  List.map (fun (_,a,b,c) -> a,b,c) clauses

let pp_program (pp : pp_ctx:pp_ctx -> depth:int -> _) fmt (compiler_state, { Assembled.clauses; symbols }) =

  let clauses = handle_clause_graftin clauses in

  let pp_ctx = {
    uv_names = ref (IntMap.empty, 0);
    table = SymbolMap.compile symbols;
  } in
  Format.fprintf fmt "@[<v>";
  List.iter (fun (name,predicate,{ depth; args; hyps; loc; timestamp }) ->
    Format.fprintf fmt "@[<h>%% %a [%a] %a@]@;"
      Format.(pp_print_option Loc.pp) loc
      Format.(pp_print_list ~pp_sep:(fun fmt () -> pp_print_string fmt "; ") pp_print_int) timestamp
      Format.(pp_print_option pp_print_string) name;
    Fmt.fprintf fmt "@[<hov 1>%a :- %a.@]@;"
      (pp ~depth ~pp_ctx) (if args = [] then D.Const predicate else D.mkApp predicate (List.hd args) (List.tl args))
      (pplist (pp ~depth ~pp_ctx) ", ") hyps)
    clauses;
  Format.fprintf fmt "@]"
;;

let pp_goal pp fmt {  WithMain.compiler_state; initial_goal; symbols } =
  let pp_ctx = {
    uv_names = ref (IntMap.empty, 0);
    table = SymbolMap.compile symbols;
  } in
  Format.fprintf fmt "@[<v>";
  Format.fprintf fmt "%a.@;" (pp ~pp_ctx ~depth:0) initial_goal;
  Format.fprintf fmt "@]"
;;

let elpi ~language:_ state loc s =
  let module P = (val option_get ~err:"No parser" (State.get parser state)) in
  let ast = P.goal ~loc ~text:s in
  let term = Scope_Quotation_Macro.scope_loc_term ~state ast in
  { ScopedTerm.SimpleTerm.it = Opaque (ScopedTerm.in_scoped_term term); loc = term.loc }

exception RelocationError of string

let relocate_closed_term ~from:symbol_table ~to_:(_,{ Assembled.symbols }) (t : term) : term =
  let relocate c =
    let s = D.Constants.Map.find c symbol_table.c2s in
    let c = SymbolMap.get_global_symbol symbols (F.from_string s) in
    match c with
    | Some x -> x
    | None -> raise (RelocationError (Format.asprintf "Relocation: unknown global %s" s))
    in
  let rec rel = function
    | Const c when c < 0 -> Const (relocate c)
    | Const _ as x -> x
    | App(c,x,xs) when c < 0 -> App(relocate c,rel x,List.map rel xs)
    | App(c,x,xs) -> App(c,rel x, List.map rel xs)
    | Cons(x,y) -> Cons(rel x, rel y)
    | Lam t -> Lam(rel t)
    | CData _ as x -> x
    | Builtin(c,l) -> Builtin(relocate c,List.map rel l)
    | (Nil | Discard) as x -> x
    | Arg _ | AppArg _ | UVar _ | AppUVar _ -> assert false
  in
    rel t
  
let relocate_closed_term ~from ~to_ t =
  try Result.Ok(relocate_closed_term ~from ~to_ t)
  with RelocationError s -> Result.Error s

let lookup_query_predicate _ _ = assert false