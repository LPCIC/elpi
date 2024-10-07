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

let rec filter_if ({ defined_variables } as flags) proj = function
  | [] -> []
  | c :: rest ->
    match proj c with
    | None -> c :: filter_if flags proj rest
    | Some e when StrSet.mem e defined_variables -> c :: filter_if flags proj rest
    | Some _ -> filter_if flags proj rest

(* Symbol table of a compilation unit (part of the compiler state).

   The initial value is taken from Data.Global_symbols, then both global
   names and local ones are allocated (hashconsed) in this table.

   Given a two symbols table (base and second) we can obtain a new one
   (updated base) via [build_shift] that contains the union of the symbols
   and a relocation to be applied to a program that lives in the second table.
   The code applying the shift is also supposed to re-hashcons and recognize
   builtins.
*)
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

let global_table () =
  {
    ast2ct = StrMap.fold (fun s v m -> F.Map.add (F.from_string s) v m) D.Global_symbols.table.s2ct F.Map.empty;
    c2t = D.Constants.Map.map (fun x -> snd @@ StrMap.find x D.Global_symbols.table.s2ct) D.Global_symbols.table.c2s;
    c2s = D.Global_symbols.table.c2s;
    last_global = D.Global_symbols.table.last_global;
    locked = false;
    uuid = Util.UUID.make ();
    frozen = false;
  }

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

end

module Builtins : sig

  val all : D.State.t -> D.Constants.Set.t
  val register : D.State.t -> D.BuiltInPredicate.t -> D.State.t
  val is_declared : D.State.t -> D.constant -> bool
  val is_declared_str : D.State.t -> string -> bool

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


let register state (D.BuiltInPredicate.Pred(s,_,_) as b) =
  if s = "" then anomaly "Built-in predicate name must be non empty";
  if not (D.State.get D.while_compiling state) then
    anomaly "Built-in can only be declared at compile time";
  let state, idx = Symbols.allocate_global_symbol_str state s in
  let declared = (D.State.get builtins state).constants in
  if D.Constants.Set.mem idx declared then
    anomaly ("Duplicate built-in predicate " ^ s);
  D.State.update builtins state (fun { names; constants; code } ->
    { names = StrSet.add s names;
      constants = D.Constants.Set.add idx constants;
      code = b :: code;
    })
;;

let is_declared_str state x =
  let declared = (D.State.get builtins state).names in
  StrSet.mem x declared
  || x == Symbols.(show state D.Global_symbols.declare_constraintc)
  || x == Symbols.(show state D.Global_symbols.print_constraintsc)
  || x == Symbols.(show state D.Global_symbols.cutc)
  || x == Symbols.(show state D.Global_symbols.eqc)
  || x == Symbols.(show state D.Global_symbols.findall_solutionsc)
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

let raw_mk_Arg s n  { c2i; nargs; i2n; n2t; n2i } =
  let s, nc = Symbols.allocate_Arg_symbol s nargs in
  let n' = Symbols.get_canonical s nc in
  let i2n = IntMap.add nargs n i2n in
  let c2i = D.Constants.Map.add nc nargs c2i in
  let n2t = StrMap.add n (n',nc) n2t in
  let n2i = StrMap.add n nargs n2i in
  let nargs = nargs + 1 in
  s, { c2i; nargs; i2n; n2t; n2i }, (n', nc)

type preterm = {
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
[@@ deriving show, ord]

(****************************************************************************
  Intermediate program representation
 ****************************************************************************)

open Data
module C = Constants

type block_constraint = {
   clique : constant list;
   ctx_filter : constant list;
   rules : prechr_rule list
}
[@@deriving show, ord]

module Types = struct

type typ = {
  tindex : Ast.Structured.tattribute;
  decl : type_declaration
}
[@@deriving show, ord]

module Set = Util.Set.Make(struct
  type t = typ
  let compare = compare_typ
  let show = show_typ
  let pp = pp_typ
end)

type types = {
  set : Set.t;
  lst : typ list;
  def : typ;
} [@@deriving show, ord]

let make t = { set = Set.singleton t; lst = [t]; def = t }

let merge t1 t2 =
  let l2 = List.filter (fun t -> not @@ Set.mem t t1.set) t2.lst in
  match l2 with
  | [] -> t1
  | _ :: _ ->
    {
      set = Set.union t1.set t2.set;
      lst = t1.lst @ l2;
      def = t2.def;
    }

let smart_map (f : typ -> typ) (t : types) : types =
  let set' = Set.map f t.set in
  let lst' = smart_map f t.lst in
  let def' = f t.def in
  if set' == t.set && lst' == t.lst && def' == t.def then t
  else { set = set'; lst = lst'; def = def' }

let append x t = {
  set = Set.add x t.set;
  lst = x :: t.lst;
  def = t.def;
}

let fold f accu t = List.fold_left f accu t.lst
let iter f t = List.iter f t.lst
let for_all f t = List.for_all f t.lst

end

module Structured = struct

type program = {
  pbody : pbody;
  local_names : int;
  toplevel_macros : macro_declaration;
}
and pbody = {
  types : Types.types C.Map.t;
  type_abbrevs : type_abbrev_declaration C.Map.t;
  modes : (mode * Loc.t) C.Map.t;
  functionality : C.Set.t;
  body : block list;
  (* defined (global) symbols (including in sub blocks) *)
  symbols : C.Set.t;
}
and block =
  | Clauses of (preterm,Ast.Structured.attribute) Ast.Clause.t list (* TODO: use a map : predicate -> clause list to speed up insertion *)
  | Namespace of string * pbody
  | Shorten of C.t Ast.Structured.shorthand list * pbody
  | Constraints of block_constraint * pbody
and typ = {
  tindex : Ast.Structured.tattribute;
  decl : type_declaration
}
[@@deriving show, ord]

end

module Flat = struct

type program = {
  types : Types.types C.Map.t;
  type_abbrevs : type_abbrev_declaration C.Map.t;
  modes : (mode * Loc.t) C.Map.t;
  functionality : C.Set.t;
  clauses : (preterm,Ast.Structured.attribute) Ast.Clause.t list;
  chr : block_constraint list;
  local_names : int;
}
[@@deriving show]

end

module Assembled = struct

type program = {
  types : Types.types C.Map.t;
  type_abbrevs : type_abbrev_declaration C.Map.t;
  modes : (mode * Loc.t) C.Map.t;
  functionality: C.Set.t;
  clauses : (preterm,attribute) Ast.Clause.t list;
  prolog_program : index;
  indexing : (mode * indexing) C.Map.t;
  chr : block_constraint list;
  local_names : int;

  toplevel_macros : macro_declaration;
}
and attribute = {
  id : string option;
  timestamp : grafting_time;
  insertion : Ast.Structured.insertion option;
}
[@@deriving show]

let empty () = {
  types = C.Map.empty;
  type_abbrevs = C.Map.empty;
  modes = C.Map.empty;
  functionality = C.Set.empty;
  clauses = [];
  prolog_program = { idx = Ptmap.empty; time = 0; times = StrMap.empty };
  indexing = C.Map.empty;
  chr = [];
  local_names = 0;
  toplevel_macros = F.Map.empty;
}

end

type compilation_unit = {
  symbol_table : Symbols.pruned_table;
  version : string;
  code : Flat.program;
}
[@@deriving show]

type builtins = string * Data.BuiltInPredicate.declaration list

type header = State.t * compilation_unit * macro_declaration
type program = State.t * Assembled.program


module WithMain = struct

(* The entire program + query, but still in "printable" format *)
type 'a query = {
  types : Types.types C.Map.t;
  type_abbrevs : type_abbrev_declaration C.Map.t;
  modes : mode C.Map.t;
  functionality : C.Set.t;
  clauses : (preterm,Assembled.attribute) Ast.Clause.t list;
  prolog_program : index;
  chr : block_constraint list;
  initial_depth : int;
  query : preterm;
  query_arguments : 'a Query.arguments [@opaque];
  (* We pre-compile the query to ease the API *)
  initial_goal : term; assignments : term StrMap.t;
  compiler_state : State.t;
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
      | (External | Index _ | Functional) as a :: _-> illegal_err a
    in
    let attributes = aux_attrs { insertion = None; id = None; ifexpr = None } attributes in
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
      | (Before _ | After _ | Replace _ | Remove _ | External | Index _ | Functional) as a :: _ -> illegal_err a 
    in
    let cid = Loc.show loc in 
    { c with Chr.attributes = aux_chr { cid; cifexpr = None } attributes }

  let structure_type_attributes { Type.attributes; loc; name; ty } =
    let duplicate_err s =
      error ~loc ("duplicate attribute " ^ s) in
    let illegal_err a =
      error ~loc ("illegal attribute " ^ show_raw_attribute a) in
    let rec aux_tatt r = function
      | [] -> r
      | External :: rest ->
         begin match r with
           | None -> aux_tatt (Some Structured.External) rest
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
           | None -> aux_tatt (Some (Structured.Index(i,it))) rest
           | Some (Structured.Index _) -> duplicate_err "index"
           | Some _ -> error ~loc "external predicates cannot be indexed"
         end
      | Functional :: rest ->
          begin match r with
           | None -> aux_tatt (Some Functional) rest
           | Some (Structured.Index _) -> duplicate_err "index"
           | Some _ -> error ~loc "external predicates cannot be indexed"

         end
      | (Before _ | After _ | Replace _ | Remove _ | Name _ | If _) as a :: _ -> illegal_err a 
    in
    let attributes = aux_tatt None attributes in
    let attributes =
      match attributes with
      | None -> Structured.Index([1],None)
      | Some x -> x in
    { Type.attributes; loc; name; ty }


  let run _ dl =
    let rec aux_run ns blocks clauses macros types tabbrs modes functionality locals chr accs = function
      | Program.Ignored _ :: rest ->
          aux_run ns blocks clauses macros types tabbrs modes functionality locals chr accs rest
      | (Program.End _ :: _ | []) as rest ->
          { body = List.rev (cl2b clauses @ blocks);
            types = List.rev types;
            type_abbrevs = List.rev tabbrs;
            macros = List.rev macros;
            modes = List.rev modes;
            functionality = List.rev functionality },
          locals,
          List.rev chr,
          rest
      | Program.Begin loc :: rest ->
          let p, locals1, chr1, rest = aux_run ns [] [] [] [] [] [] [] [] [] accs rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside an anonymous block";
          aux_end_block loc ns (Locals(locals1,p) :: cl2b clauses @ blocks)
            [] macros types tabbrs modes functionality locals chr accs rest
      | Program.Constraint (loc, ctx_filter, clique) :: rest ->
          if chr <> [] then
            error "Constraint blocks cannot be nested";
          let p, locals1, chr, rest = aux_run ns [] [] [] [] [] [] [] [] [] accs rest in
          if locals1 <> [] then
            error "locals cannot be declared inside a Constraint block";
          aux_end_block loc ns (Constraints({ctx_filter;clique;rules=chr},p) :: cl2b clauses @ blocks)
            [] macros types tabbrs modes functionality locals [] accs rest
      | Program.Namespace (loc, n) :: rest ->
          let p, locals1, chr1, rest = aux_run (n::ns) [] [] [] [] [] [] [] [] [] StrSet.empty rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside a namespace block";
          if locals1 <> [] then
            error "locals cannot be declared inside a namespace block";
          aux_end_block loc ns (Namespace (n,p) :: cl2b clauses @ blocks)
            [] macros types tabbrs modes functionality locals chr accs rest
      | Program.Shorten (loc,[]) :: _ ->
          anomaly ~loc "parser returns empty list of shorten directives"
      | Program.Shorten (loc,directives) :: rest ->
          let shorthand (full_name,short_name) = { iloc = loc; full_name; short_name } in
          let shorthands = List.map shorthand directives in
          let p, locals1, chr1, rest = aux_run ns [] [] [] [] [] [] [] [] [] accs rest in
          if locals1 <> [] then
            error "locals cannot be declared after a shorthand";
          if chr1 <> [] then
            error "CHR cannot be declared after a shorthand";
          aux_run ns ((Shorten(shorthands,p) :: cl2b clauses @ blocks))
            [] macros types tabbrs modes functionality locals chr accs rest

      | Program.Accumulated (_,[]) :: rest ->
          aux_run ns blocks clauses macros types tabbrs modes functionality locals chr accs rest

      | Program.Accumulated (loc,(digest,a) :: more) :: rest ->
          let rest = Program.Accumulated (loc, more) :: rest in
          let digest = String.concat "." (digest :: List.map F.show ns) in
          if StrSet.mem digest accs then
            aux_run ns blocks clauses macros types tabbrs modes functionality locals chr accs rest
          else
            aux_run ns blocks clauses macros types tabbrs modes functionality locals chr
              (StrSet.add digest accs)
              (Program.Begin loc :: a @ Program.End loc :: rest)

      | Program.Clause c :: rest ->
          let c = structure_clause_attributes c in
          aux_run ns blocks (c::clauses) macros types tabbrs modes functionality locals chr accs rest
      | Program.Macro m :: rest ->
          aux_run ns blocks clauses (m::macros) types tabbrs modes functionality locals chr accs rest
      | Program.Pred t :: rest ->
          let t = structure_type_attributes t in
          let types = if t.attributes <> Functional && List.mem t types then types else t :: types in
          let functionality = if t.attributes = Functional then t.name :: functionality else functionality in
          aux_run ns blocks clauses macros types tabbrs (t::modes) functionality locals chr accs rest
      | Program.Type [] :: rest ->
          aux_run ns blocks clauses macros types tabbrs modes functionality locals chr accs rest
      | Program.Type (t::ts) :: rest ->          
          let t = structure_type_attributes t in
          if t.attributes = Functional then error ~loc:t.loc "functional attribute only applies to pred";
          let types = if List.mem t types then types else t :: types in
          aux_run ns blocks clauses macros types tabbrs modes functionality locals chr accs
            (Program.Type ts :: rest)
      | Program.TypeAbbreviation abbr :: rest ->
          aux_run ns blocks clauses macros types (abbr :: tabbrs) modes functionality locals chr accs rest
      | Program.Local l :: rest ->
          aux_run ns blocks clauses macros types tabbrs modes functionality (l@locals) chr accs rest
      | Program.Chr r :: rest ->
          let r = structure_chr_attributes r in
          aux_run ns blocks clauses macros types tabbrs modes functionality locals (r::chr) accs rest

    and aux_end_block loc ns blocks clauses macros types tabbrs modes functionality locals chr accs rest =
      match rest with
      | Program.End _ :: rest ->
          aux_run ns blocks clauses macros types tabbrs modes functionality locals chr accs rest
      | _ -> error ~loc "matching } is missing"

    in
    let blocks, locals, chr, rest = aux_run [] [] [] [] [] [] [] [] [] [] StrSet.empty dl in
    begin match rest with
    | [] -> ()
    | Program.End loc :: _ -> error ~loc "extra }"
    | _ -> assert false
    end;
    if chr <> [] then
      error "CHR cannot be declared outside a Constraint block";
    if locals <> [] then
      error "locals cannot be declared outside an anonymous block";
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

  let compile_singlequote state x =
    match State.get singlequote state with
    | None -> let state, (_,t) = Symbols.allocate_global_symbol state x in state, t
    | Some f -> f state x
  let compile_backtick state x =
    match State.get backtick state with
    | None -> let state, (_,t) = Symbols.allocate_global_symbol state x in state, t
    | Some f -> f state x

end

module ToDBL : sig
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
  val merge_functionality : C.Set.t -> C.Set.t -> C.Set.t
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
    | TPred (_, m) ->
        let m = List.rev m |> List.tl |> List.rev in
        to_mode_rec_aux m
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
let get_Arg = ToDBL.get_Arg


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
    let functionality = apply_subst_functionality ~live_symbols empty_subst functionality in
    let types, type_abbrevs, modes, clauses, chr =
      compile_body live_symbols state local_names types type_abbrevs modes [] [] empty_subst body in
    !live_symbols, toplevel_macros, { Flat.types;
      type_abbrevs;
      modes;
      functionality;
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
      functionality;
      clauses;
      chr;
      local_names;
    } =
      let f = [], f in
    {
      Flat.types = apply_subst_types state f types;
      type_abbrevs = apply_subst_type_abbrevs state f type_abbrevs;
      modes = apply_subst_modes f modes;
      functionality = apply_subst_functionality f functionality;
      clauses = apply_subst_clauses state f clauses;
      chr = smart_map (apply_subst_chr state f) chr;
      local_names;
    }



end (* }}} *)

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

  let rec read_ty = function
    | TApp(c,x,[y]) when c == D.Global_symbols.variadic -> `Variadic (read_ty x,read_ty y)
    | TArr(x,y) -> 
        let ty_x = read_ty x in
        begin match read_ty y with
        | `Arrow(tys,ty) -> `Arrow (ty_x :: tys, ty)
        | ty -> `Arrow([ty_x], ty) end
    | TConst x when x == D.Global_symbols.propc -> `Prop
    | TPred (_, l) -> `Arrow (List.map (fun (_, t) -> read_ty t) l, `Prop)
    | _ -> `Unknown

  let type_of_const types c =
    try
      let { Types.decl = { ttype } } = (C.Map.find c types).Types.def in
      read_ty ttype.ttype
    with
      Not_found -> `Unknown

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
    let ty = type_of_const types c in
    let ty_mode, mode =
      match modes c with
      | l -> `Arrow(List.length l,`Prop), l
      | exception Not_found -> `Unknown, [] in
    let nargs = List.length args in
    let missing_args =
      match ty_mode, ty with
      | `Unknown,`Arrow(args,_) -> List.length args - nargs
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
             | (`Variadic(_,`Prop) | `Arrow([],`Prop)), [] -> [],[],true
             | _, [] -> [],[],false
             | `Variadic(`Prop,_), a1 :: an ->
                   ([],spaux1_prop ctx a1) @@@ aux_spaux ty an
             | `Arrow(`Prop :: ty,c), a1 :: an ->
                   ([],spaux1_prop ctx a1) @@@ aux_spaux (`Arrow(ty,c)) an
             | `Arrow((_ :: _ as ty),c), a1 :: an ->
                   let spills, a1 = spaux ctx a1 in
                   let ty = drop (size_outermost_spill spills ~default:1) ty in
                   (spills, a1) @@@ aux_spaux (`Arrow(ty,c)) an
             | _, a1 :: an -> spaux ctx a1 @@@ aux_spaux ty an
           in
             aux_spaux (type_of_const types hd) args in
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



let stack_term_of_preterm ~depth:arg_lvl state { term = t; amap = { c2i } } =
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
  !state, t
;;

(* This is marshalable *)

module Assemble : sig

  val assemble : flags -> State.t -> Assembled.program -> compilation_unit list -> State.t * Assembled.program

end = struct (* {{{ *)

let compile_clause_attributes ({ Ast.Clause.attributes = { Ast.Structured.id }} as c) timestamp insertion =
  { c with Ast.Clause.attributes = { Assembled.id; timestamp; insertion }}

  (* let shift_pp fmt ({ Data.Constants.c2s},s,{ Data.Constants.c2s = c2s2 }) =
    Format.fprintf fmt "{{ @[<hov 2>";
    IntMap.iter (fun k v ->
      Format.fprintf fmt "(%s)%a ->@ (%s)%a;@ "
        (Hashtbl.find c2s k) Int.pp k (Hashtbl.find c2s2 v) Int.pp v) s;
    Format.fprintf fmt "@] }}" *)
  let clause_ifexpr { Ast.Clause.attributes = { Ast.Structured.ifexpr } } = ifexpr

  let chose_indexing state predicate l k =
    let all_zero = List.for_all ((=) 0) in
    let rec check_map default argno = function
      (* TODO: @FissoreD here we should raise an error if n > arity of the predicate? *)
      | [] -> error ("Wrong indexing for " ^ Symbols.show state predicate ^ ": no argument selected.")
      | 0 :: l -> check_map default (argno+1) l
      | 1 :: l when all_zero l -> MapOn argno
      | _ -> default ()
    in
    match k with
    | Some Ast.Structured.DiscriminationTree -> DiscriminationTree l
    | Some HashMap -> Hash l
    | None -> check_map (fun () -> DiscriminationTree l) 0 l
    | Some Map -> check_map (fun () ->
        error ("Wrong indexing for " ^ Symbols.show state predicate ^
                ": Map indexes exactly one argument at depth 1")) 0 l
  
  let update_indexing state index modes types old_idx =
    let check_if_some_clauses_already_in ~loc predicate =
      if Ptmap.mem predicate index then
         error ~loc @@ "Some clauses for " ^ Symbols.show state predicate ^
           " are already in the program, changing the indexing a posteriori is not allowed."
      in  
    let add_indexing_for ~loc name tindex map =
      let mode = try fst @@ C.Map.find name modes with Not_found -> [] in
      let declare_index, index =
        match tindex with
        | Some (Ast.Structured.Index(l,k)) -> true, chose_indexing state name l k
        | _ -> false, chose_indexing state name [1] None in
      try
        let _, old_tindex =
          try C.Map.find name map
          with Not_found -> C.Map.find name old_idx in
        if old_tindex <> index then
          if old_tindex <> MapOn 1 && declare_index then
            error ~loc ("multiple and inconsistent indexing attributes for " ^
                      Symbols.show state name)
          else
            if declare_index then begin
              check_if_some_clauses_already_in ~loc name;
              C.Map.add name (mode,index) map
            end else map
        else
          map
      with Not_found ->
        check_if_some_clauses_already_in ~loc name;
        C.Map.add name (mode,index) map in
        
    let map = C.Map.fold (fun tname l acc -> Types.fold (fun acc { Types.tindex; decl = { tloc } } -> add_indexing_for ~loc:tloc tname (Some tindex) acc) acc l) types C.Map.empty in
    let map = C.Map.fold (fun k (_,loc) m -> add_indexing_for ~loc k None m) modes map in
    map, C.Map.union (fun _ _ _ -> assert false) map old_idx
     
let compile_clause modes initial_depth (state, index, clauses)
    ({ Ast.Clause.body = ({ amap = { nargs }} as body); loc; attributes } as c)
  =
  let state, body = stack_term_of_preterm ~depth:0 state body in
  let modes x = try fst @@ C.Map.find x modes with Not_found -> [] in
  let name = attributes.Ast.Structured.id in
  let (p,cl), _, morelcs =
    try R.CompileTime.clausify1 ~loc ~modes ~nargs ~depth:initial_depth body
    with D.CannotDeclareClauseForBuiltin(loc,c) ->
      error ?loc ("Declaring a clause for built in predicate " ^ Symbols.show state c)
    in
  if morelcs <> 0 then error ~loc "sigma in a toplevel clause is not supported";
  let graft = attributes.Ast.Structured.insertion in
   (* Printf.eprintf "adding clause from %s %s\n" (Loc.show loc) (Option.fold ~none:"" ~some:String.show name);  *)
  let index = R.CompileTime.add_to_index ~depth:initial_depth ~predicate:p ~graft cl name index in
  state, index, (compile_clause_attributes c cl.timestamp graft) :: clauses


let assemble flags state code  (ul : compilation_unit list) =
  let local_names = code.Assembled.local_names in

  let state, index, indexing, clauses, types, type_abbrevs, modes, functionality, chr_rev =
    List.fold_left (fun (state, index, idx1, clauses, t1, ta1, m1, f1, c1) ({ symbol_table; code }  as _u) ->
      let state, { Flat.clauses = cl2; types = t2; type_abbrevs = ta2; modes = m2; functionality = f2; chr = c2; } =
        let state, shift = Stdlib.Result.get_ok @@ Symbols.build_shift ~flags ~base:state symbol_table in
        let code =
          if C.Map.is_empty shift then code
          else Flatten.relocate state shift code in
        state, code in
      let modes = ToDBL.merge_modes state m1 m2 in
      let functionality = ToDBL.merge_functionality f1 f2 in
      let type_abbrevs = ToDBL.merge_type_abbrevs state ta1 ta2 in
      let types = ToDBL.merge_types state t1 t2 in

      (* no mode discrepancy tested by merge_modes/types *)
      let new_indexing, idx2 = update_indexing state index.idx m2 t2 idx1 in

      let index = R.CompileTime.update_indexing new_indexing index in

      let cl2 = filter_if flags clause_ifexpr cl2 in
      let cl2 = List.map (Spill.spill_clause state ~types ~modes:(fun c -> fst @@ C.Map.find c modes)) cl2 in
      let c2 = List.map (Spill.spill_chr state ~types ~modes:(fun c -> fst @@ C.Map.find c modes)) c2 in
      let state, index,clauses =
        List.fold_left (compile_clause modes local_names) (state,index,clauses) cl2 in
      
      state, index, idx2, clauses, types, type_abbrevs, modes, functionality, c2 :: c1
    ) (state, code.prolog_program, code.indexing, code.clauses, code.types, code.type_abbrevs, code.modes, code.functionality, []) ul in
  let prolog_program = index in
  let chr = List.concat (code.chr :: List.rev chr_rev) in
  let chr =
    let pifexpr { pifexpr } = pifexpr in
    List.map (fun {ctx_filter;clique;rules} -> {ctx_filter;clique;rules=filter_if flags pifexpr rules}) chr in
  state, { Assembled.clauses; indexing; prolog_program; types; type_abbrevs; modes; functionality; chr; local_names = code.local_names; toplevel_macros = code.toplevel_macros }

end (* }}} *)


(****************************************************************************
  API
 ****************************************************************************)

let rec constants_of acc = function
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
  f x

(* Compiler passes *)
let unit_or_header_of_ast { print_passes } s ?(toplevel_macros=F.Map.empty) p =

  if print_passes then
    Format.eprintf "== AST ================@\n@[<v 0>%a@]@\n"
      Ast.Program.pp p;

  let p = RecoverStructure.run s p in

  if print_passes then
    Format.eprintf "== Ast.Structured ================@\n@[<v 0>%a@]@\n"
      (w_symbol_table s Ast.Structured.pp_program) p;

  let s, p = ToDBL.run s ~toplevel_macros p in

  if print_passes then
    Format.eprintf "== Structured ================@\n@[<v 0>%a@]@\n"
      (w_symbol_table s Structured.pp_program) p;

  let alive, toplevel_macros, p = Flatten.run s p in

  if print_passes then
    Format.eprintf "== Flat ================@\n@[<v 0>%a@]@\n"
      (w_symbol_table s Flat.pp_program) p;

  s, {
    version = "%%VERSION_NUM%%";
    code = p;
    symbol_table = Symbols.prune (State.get Symbols.table s) ~alive
  }, toplevel_macros
;;

let print_unit { print_units } x =
    if print_units then
      let b1 = Marshal.to_bytes x.code [] in
      let b2 = Marshal.to_bytes x.symbol_table [] in
      Printf.eprintf "== UNIT =================\ncode: %dk (%d clauses)\nsymbols: %dk (%d entries: %s)\n%!"
        (Bytes.length b1 / 1024) (List.length x.code.Flat.clauses)  (Bytes.length b2 / 1024)
        (Symbols.size x.symbol_table)
        (String.concat ", " (List.sort compare (Symbols.symbols x.symbol_table)))
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
  let state = State.set Symbols.table state (Symbols.global_table ()) in
  let state =
    List.fold_left (fun state (_,decls) ->
      List.fold_left (fun state -> function
      | Data.BuiltInPredicate.MLCode (p,_) -> Builtins.register state p
      | Data.BuiltInPredicate.MLData _ -> state
      | Data.BuiltInPredicate.MLDataC _ -> state
      | Data.BuiltInPredicate.LPCode _ -> state
      | Data.BuiltInPredicate.LPDoc _ -> state) state decls) state builtins in
  let state, u, toplevel_macros = unit_or_header_of_ast flags state ast in
  print_unit flags u;
  state, u, toplevel_macros

let unit_of_ast ~flags ~header:(s, (header : compilation_unit), toplevel_macros) p : compilation_unit =
  let _, u, _ = unit_or_header_of_ast flags s ~toplevel_macros p in
  print_unit flags u;
  u

let assemble_units ~flags ~header:(s,h,toplevel_macros) units : program =

  let nunits_with_locals =
    (h :: units) |> List.filter (fun {code = { Flat.local_names = x }} -> x > 0) |> List.length in

  if nunits_with_locals > 0 then
    error "Only 1 compilation unit is supported when local directives are used";

  let init = { (Assembled.empty ()) with toplevel_macros; local_names = h.code.local_names } in

  let s, p = Assemble.assemble flags s init (h :: units) in

  let { print_passes } = flags in

  if print_passes then
    Format.eprintf "== Assembled ================@\n@[<v 0>%a@]@\n"
      (w_symbol_table s Assembled.pp_program) p;

 s, p
;;

let append_units ~flags ~base:(s,p) units : program =
  let s, p = Assemble.assemble flags s p units in
  let { print_passes } = flags in

  if print_passes then
    Format.eprintf "== Assembled ================@\n@[<v 0>%a@]@\n"
      (w_symbol_table s Assembled.pp_program) p;

  s, p

let program_of_ast ~flags ~header p : program =
  let u = unit_of_ast ~flags ~header p in
  assemble_units ~flags ~header [u]

let is_builtin state tname =
  Builtins.is_declared state tname

let check_all_builtin_are_typed state types =
   Constants.Set.iter (fun c ->
     if not (match C.Map.find c types with
     | l -> l |> Types.for_all (fun { Types.tindex;_} -> tindex = Ast.Structured.External)
     | exception Not_found -> false) then
       error ("Built-in without external type declaration: " ^ Symbols.show state c))
   (Builtins.all state);
  C.Map.iter (fun tname tl -> tl |> Types.iter (fun { Types.tindex; decl = { tname; tloc }} ->
    if tindex = Ast.Structured.External && not (is_builtin state tname) then
      error ~loc:tloc ("external type declaration without Built-in: " ^
            Symbols.show state tname)))
  types
;;

let check_no_regular_types_for_builtins state types =
  C.Map.iter (fun tname l -> l |> Types.iter (fun {Types.tindex; decl = { tloc } } ->
    if tindex <> Ast.Structured.External && is_builtin state tname then
      anomaly ~loc:tloc ("type declaration for Built-in " ^
            Symbols.show state tname ^ " must be flagged as external");
 )) types


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
  let initial_depth = assembled_program.Assembled.local_names in
  let types = assembled_program.Assembled.types in
  let type_abbrevs = assembled_program.Assembled.type_abbrevs in
  let modes = C.Map.map fst @@ assembled_program.Assembled.modes in
  let active_macros = assembled_program.Assembled.toplevel_macros in
  let state, query =
    ToDBL.query_preterm_of_ast ~depth:initial_depth active_macros compiler_state t in
  let query = Spill.spill_preterm state types (fun c -> C.Map.find c modes) query in
  let query_env = Array.make query.amap.nargs D.dummy in
  let state, queryt = stack_term_of_preterm ~depth:initial_depth state query in
  let initial_goal =
    R.move ~argsdepth:initial_depth ~from:initial_depth ~to_:initial_depth query_env
      queryt in
  let assignments = StrMap.map (fun i -> query_env.(i)) query.amap.n2i in
  {
    WithMain.types;
    modes;
    functionality = assembled_program.Assembled.functionality;
    type_abbrevs;
    prolog_program = assembled_program.Assembled.prolog_program;
    clauses = assembled_program.Assembled.clauses;
    chr = assembled_program.Assembled.chr;
    initial_depth;
    query;
    query_arguments = Query.N;
    initial_goal;
    assignments;
    compiler_state = state |> (uvbodies_of_assignments assignments) |> state_update;
  }

let query_of_term (compiler_state, assembled_program) f =
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
    functionality = assembled_program.functionality;
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


let query_of_data (state, p) loc (Query.Query { arguments } as descr) =
  let query = query_of_term (state, p) (fun ~depth state ->
    let state, term, gls = R.embed_query ~mk_Arg ~depth state descr in
    state, (loc, term), gls) in
  { query with query_arguments = arguments }

let lookup_query_predicate (state, p) pred =
  let state, pred = Symbols.allocate_global_symbol_str state pred in
  (state, p), pred

module Compiler : sig

  (* Translates preterms in terms and AST clauses into clauses (with a key,
   * subgoals, etc *)

  val run : 'a query -> 'a executable

end = struct (* {{{ *)

let compile_chr depth state
    { pto_match; pto_remove; pguard; pnew_goal; pamap; pname; pcloc = loc }
=
  if depth > 0 then error ~loc "CHR: rules and locals are not supported";
  let key_of_sequent { pconclusion } =
    match pconclusion with
    | Const x -> x
    | App(x,_,_) -> x
    | _ -> error ~loc "CHR: rule without head symbol" in
  let stack_term_of_preterm s term =
    stack_term_of_preterm ~depth:0 s { term; amap = pamap; loc; spilling = true } in
  let stack_sequent_of_presequent s { pcontext; pconclusion; peigen } =
    let s, context = stack_term_of_preterm s pcontext in
    let s, conclusion = stack_term_of_preterm s pconclusion in
    let s, eigen = stack_term_of_preterm s peigen in
    s, { CHR.context; conclusion; eigen } in
  let all_sequents = pto_match @ pto_remove in
  let pattern = List.map key_of_sequent all_sequents in
  let state, to_match = map_acc stack_sequent_of_presequent state pto_match in
  let state, to_remove = map_acc stack_sequent_of_presequent state pto_remove in
  let state, guard = option_mapacc stack_term_of_preterm state pguard in
  let state, new_goal = option_mapacc stack_sequent_of_presequent state pnew_goal in
  state, {
    CHR.to_match;
        to_remove;
        patsno = List.(length pto_match + length pto_remove);
        guard;
        new_goal;
        nargs = pamap.nargs;
        pattern;
        rule_name = pname;
        rule_loc = loc;
      }
;;



let check_rule_pattern_in_clique state clique { D.CHR.pattern; rule_name } =
  try
    let outside =
      List.find (fun x -> not (D.CHR.in_clique clique x)) pattern in
    error ("CHR rule " ^ rule_name ^ ": matches " ^ Symbols.show state outside ^
      " which is not a constraint on which it is applied. Check the list of predicates after the \"constraint\" keyword.");
  with Not_found -> ()

let run
  {
    WithMain.types;
    modes;
    clauses = _;
    prolog_program;
    chr;
    initial_depth;
    initial_goal;
    assignments;
    compiler_state = state;
    query_arguments;
  }
=
  check_all_builtin_are_typed state types;
  check_no_regular_types_for_builtins state types;
  (* Real Arg nodes: from "Const '%Arg3'" to "Arg 3" *)
  let state, chr =
    List.fold_left (fun (state, chr) {ctx_filter; clique; rules} ->
      let chr, clique = CHR.new_clique (Symbols.show state) ctx_filter clique chr in
      let state, rules = map_acc (compile_chr initial_depth) state rules in
      List.iter (check_rule_pattern_in_clique state clique) rules;
      state, List.fold_left (fun x y -> CHR.add_rule clique y x) chr rules)
    (state, CHR.empty) chr in
  let compiler_symbol_table = State.get Symbols.table state in
  let builtins = Hashtbl.create 17 in
  let pred_list = (State.get Builtins.builtins state).code in
  List.iter
    (fun (D.BuiltInPredicate.Pred(s,_,_) as p) ->
      let c, _ = Symbols.get_global_symbol_str state s in
      Hashtbl.add builtins c p)
    pred_list;
  let symbol_table = Symbols.compile_table compiler_symbol_table in
  {
    D.compiled_program = { index = close_index prolog_program; src = [] };
    chr;
    initial_depth;
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

let pp_program pp fmt {
    WithMain.clauses;
    initial_depth;
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
;;
let pp_goal pp fmt {
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
        let t = List.fold_left (fun acc e -> TArr (e, acc)) (List.hd l) (List.tl l) in
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

  (* Format.eprintf "Going to unfold %a\n%!" (pp_ttype) ttype;  *)  let rec aux seen = function
    | TConst c as x ->
        begin match find_opt c with
        | Some { tavalue; taparams; timestamp=time } ->
          (* Format.printf "Found a match %a\n" pp_ttype tavalue.ttype; *)
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
          (* Format.eprintf "Seen is [%a]\n%!" (Format.pp_print_list Format.pp_print_int) (C.Set.elements seen);
          Format.eprintf "Current is %d\n%!" c;
          Format.eprintf "Result is %a\n%!" pp_ttype tavalue.ttype;
          Format.eprintf "lcs is %d\n%!" lcs;
          Format.eprintf "Args are [%a]\n%!" (Format.pp_print_list pp_ttype) (t::ts); *)
          error_undefined ttime time c tavalue;
          aux time (beta tavalue.ttype (t::ts))
          (* aux (C.Set.add c seen) (R.deref_appuv ~from:lcs ~to_:lcs (t::ts) tavalue.term) *)
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
    (* Format.eprintf "Unfold result is %a\n%!" pp_ttype (aux C.Set.empty ttype); *)
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

let static_check ~exec ~checker:(state,program)
  ({ WithMain.types; type_abbrevs; functionality; modes; initial_depth; compiler_state } as q) =
  let time = `Compiletime in
  let state, p,q = quote_syntax time state q in

    (* Building type abbrev list *)
  let state, talist =
    C.Map.bindings type_abbrevs |>
    map_acc (fun state (name, { tavalue; timestamp=ttime } ) ->
      (* Printf.eprintf "Unfolding %d %s\n" name (Symbols.show compiler_state name);  *)
      let tavaluet = unfold_type_abbrevs ~is_typeabbrev:true ~compiler_state initial_depth type_abbrevs tavalue ttime in
      let state, tavaluet = quote_pretype time ~compiler_state state tavaluet in
      state, App(colonec, D.C.of_string (Symbols.show compiler_state name), [lam2forall tavaluet])) state
  in

  (* Building types *)
  let state, tlist = C.Map.fold (fun tname l (state,tl) ->
    let l = l.Types.lst in
    let state, l =
      List.rev l |> map_acc (fun state { Types.decl = { ttype; tname } } ->
        let state, c = mkQCon time ~compiler_state state ~on_type:false tname in
        (* Printf.eprintf "Working with the type %s\n" (Symbols.show compiler_state tname); *)
        let ttypet = unfold_type_abbrevs ~is_typeabbrev:false ~compiler_state initial_depth type_abbrevs ttype 0 in
        (* Format.eprintf "Going to quote_pretype %a\n%!" pp_ttype ttypet.ttype; *)
        let state, ttypet = quote_pretype time ~compiler_state state ttypet in
        state, App(colonc,c, [close_w_binder forallc ttypet ttype.tamap])) state
      in
        state, l :: tl)
      types (state,[]) in
  let tlist = List.concat (List.rev tlist) in
  
  (* Building functionality *)
  let state, functionality = C.Set.fold (fun tname (state,tl) ->
    let state, c = mkQCon time ~compiler_state state ~on_type:false tname in
    state, c :: tl) functionality (state,[]) in

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

