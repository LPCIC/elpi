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

let parser : (module Parse.Parser) option D.State.component = D.State.declare ~name:"elpi:parser"
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
  val pp_table : Format.formatter -> table -> unit
  val table : table D.State.component
  val compile_table : table -> D.symbol_table
  val lock : table -> table
  val locked : table -> bool
  val equal : table -> table -> bool
  val size : table -> int
  val prune : table -> D.Constants.Set.t -> table
  (* debug *)
  val symbols : table -> string list

  val global_table : unit -> table
  val uuid : table -> UUID.t

  val build_shift : flags:flags -> base:D.State.t -> table -> D.State.t * D.constant D.Constants.Map.t

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

let locked { locked } = locked
let lock t = { t with locked = true }
let uuid { uuid } = uuid
let equal t1 t2 =
  locked t1 && locked t2 && uuid t1 = uuid t2

let size t = D.Constants.Map.cardinal t.c2t

let symbols { c2s } =
  List.map (fun (c,s) -> s ^ ":" ^ string_of_int c) (D.Constants.Map.bindings c2s)

let prune t alive =
  { t with 
    c2s = D.Constants.Map.filter (fun k _ -> D.Constants.Set.mem k alive) t.c2s;
    c2t = D.Constants.Map.filter (fun k _ -> D.Constants.Set.mem k alive) t.c2t;
    ast2ct = F.Map.filter (fun _ (k,_) -> D.Constants.Set.mem k alive) t.ast2ct;
  }

let table = D.State.declare ~name:"elpi:compiler:symbol_table"
  ~pp:pp_table
  ~clause_compilation_is_over:(fun x -> x)
  ~goal_compilation_begins:(fun x -> x)
  ~goal_compilation_is_over:(fun ~args:_ x -> Some x)
  ~compilation_is_over:(fun x -> Some { x with frozen = true }) (* to implement read_term *)
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

let build_shift ~flags:{ print_units } ~base symbols =
  let open D.Constants in
  D.State.update_return table base (fun base ->
    (* We try hard to respect the same order if possible, since some tests
       (grundlagen) depend on this order (for performance, the constant-timestamp
       heuristic in unfolding) *)
    List.fold_left (fun (base,shift as acc) (v, t) ->
      if v < 0 then
        let name = Map.find v symbols.c2s in
        try
          let c, _ = F.Map.find (F.from_string name)  base.ast2ct in
          if c == v then acc
          else begin
            if print_units then Printf.printf "Relocate: %d -> %d (%s)\n%!" v c name;
            base, Map.add v c shift
          end
        with Not_found ->
          let base, (c,_) = allocate_global_symbol_aux (Ast.Func.from_string name) base in
          base, Map.add v c shift
      else
        if Map.mem v base.c2t then acc
        else
          let base = { base with c2t = Map.add v t base.c2t } in
          base, shift
      )
     (base,Map.empty)  (List.rev (Map.bindings symbols.c2t)))

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

let builtins : t D.State.component = D.State.declare ~name:"elpi:compiler:builtins"
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
[@@ deriving show]

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
[@@ deriving show]

type type_declaration = {
  tname : D.constant;
  ttype : preterm;
  tloc : Loc.t;
}
[@@ deriving show]

type type_abbrev_declaration = {
  taname : D.constant;
  tavalue : preterm;
  taparams : int;
  taloc : Loc.t;
}
[@@ deriving show]

type presequent = {
  peigen : D.term;
  pcontext : D.term;
  pconclusion : D.term;
}
[@@ deriving show]
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
[@@ deriving show]

(****************************************************************************
  Intermediate program representation
 ****************************************************************************)

open Data
module C = Constants

module Structured = struct

type program = {
  pbody : pbody;
  local_names : int;
  toplevel_macros : macro_declaration;
}
and pbody = {
  types : typ list;
  type_abbrevs : type_abbrev_declaration C.Map.t;
  modes : (mode * Loc.t) C.Map.t;
  body : block list;
  (* defined (global) symbols (including in sub blocks) *)
  symbols : C.Set.t;
}
and block =
  | Clauses of (preterm,Ast.Structured.attribute) Ast.Clause.t list
  | Namespace of string * pbody
  | Shorten of C.t Ast.Structured.shorthand list * pbody
  | Constraints of constant list * prechr_rule list * pbody
and typ = {
  tindex : Ast.Structured.tattribute;
  decl : type_declaration
}
[@@deriving show]

end

module Flat = struct

type program = {
  types : Structured.typ list;
  type_abbrevs : type_abbrev_declaration C.Map.t;
  modes : (mode * Loc.t) C.Map.t;
  clauses : (preterm,Ast.Structured.attribute) Ast.Clause.t list;
  chr : (constant list * prechr_rule list) list;
  local_names : int;
  symbols : C.Set.t;

  toplevel_macros : macro_declaration;
}
[@@deriving show]

end

module Assembled = struct

type program = {
  types : Structured.typ list;
  type_abbrevs : type_abbrev_declaration C.Map.t;
  modes : (mode * Loc.t) C.Map.t;
  clauses : (preterm,attribute) Ast.Clause.t list;
  chr : (constant list * prechr_rule list) list;
  local_names : int;

  toplevel_macros : macro_declaration;
}
and attribute = {
  id : string option;
}
[@@deriving show]

let empty = {
  types = [];
  type_abbrevs = C.Map.empty;
  modes = C.Map.empty;
  clauses = [];
  chr = [];
  local_names = 0;
  toplevel_macros = F.Map.empty;
}

end

type compilation_unit = {
  symbol_table : Symbols.table;
  version : string;
  code : Flat.program;
}
[@@deriving show]

type builtins = string * Data.BuiltInPredicate.declaration list

type header = State.t * compilation_unit
type program = State.t * Assembled.program


module WithMain = struct

(* The entire program + query, but still in "printable" format *)
type 'a query = {
  types : Structured.typ list;
  type_abbrevs : type_abbrev_declaration C.Map.t;
  modes : mode C.Map.t;
  clauses : (preterm,Assembled.attribute) Ast.Clause.t list;
  chr : (constant list * prechr_rule list) list;
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
    let rec aux r = function
      | [] -> r
      | Name s :: rest ->
         if r.id <> None then duplicate_err "name";
         aux { r with id = Some s } rest
      | After s :: rest ->
         if r.insertion <> None then duplicate_err "insertion";
         aux { r with insertion = Some (After s) } rest
      | Before s :: rest ->
         if r.insertion <> None then duplicate_err "insertion";
         aux { r with insertion = Some (Before s) } rest
      | If s :: rest ->
         if r.ifexpr <> None then duplicate_err "if";
         aux { r with ifexpr = Some s } rest
      | (External | Index _) as a :: _-> illegal_err a
    in
    { c with Clause.attributes =
        aux { insertion = None; id = None; ifexpr = None } attributes }

  let structure_chr_attributes ({ Chr.attributes; loc } as c) =
    let duplicate_err s =
      error ~loc ("duplicate attribute " ^ s) in
    let illegal_err a =
      error ~loc ("illegal attribute " ^ show_raw_attribute a) in
    let rec aux r = function
      | [] -> r
      | Name s :: rest ->
         aux { r with cid = s } rest
      | If s :: rest ->
         if r.cifexpr <> None then duplicate_err "if";
         aux { r with cifexpr = Some s } rest
      | (Before _ | After _ | External | Index _) as a :: _ -> illegal_err a 
    in
    let cid = Loc.show loc in 
    { c with Chr.attributes = aux { cid; cifexpr = None } attributes }

  let structure_type_attributes { Type.attributes; loc; name; ty } =
    let duplicate_err s =
      error ~loc ("duplicate attribute " ^ s) in
    let illegal_err a =
      error ~loc ("illegal attribute " ^ show_raw_attribute a) in
    let rec aux r = function
      | [] -> r
      | External :: rest ->
         begin match r with
           | None -> aux (Some Structured.External) rest
           | Some Structured.External -> duplicate_err "external"
           | Some _ -> error ~loc "external predicates cannot be indexed"
         end
      | Index i :: rest ->
         begin match r with
           | None -> aux (Some (Structured.Index i)) rest
           | Some (Structured.Index _) -> duplicate_err "index"
           | Some _ -> error ~loc "external predicates cannot be indexed"
         end
      | (Before _ | After _ | Name _ | If _) as a :: _ -> illegal_err a 
    in
    let attributes = aux None attributes in
    let attributes =
      match attributes with
      | None -> Structured.Index [1]
      | Some x -> x in
    { Type.attributes; loc; name; ty }


  let run _ dl =
    let rec aux ns blocks clauses macros types tabbrs modes locals chr accs = function
      | Program.Ignored _ :: rest ->
          aux ns blocks clauses macros types tabbrs modes locals chr accs rest
      | (Program.End _ :: _ | []) as rest ->
          { body = List.rev (cl2b clauses @ blocks);
            types = List.rev types;
            type_abbrevs = List.rev tabbrs;
            macros = List.rev macros;
            modes = List.rev modes },
          locals,
          List.rev chr,
          rest
      | Program.Begin loc :: rest ->
          let p, locals1, chr1, rest = aux ns [] [] [] [] [] [] [] [] accs rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside an anonymous block";
          aux_end_block loc ns (Locals(locals1,p) :: cl2b clauses @ blocks)
            [] macros types tabbrs modes locals chr accs rest
      | Program.Constraint (loc, f) :: rest ->
          if chr <> [] then
            error "Constraint blocks cannot be nested";
          let p, locals1, chr, rest = aux ns [] [] [] [] [] [] [] [] accs rest in
          if locals1 <> [] then
            error "locals cannot be declared inside a Constraint block";
          aux_end_block loc ns (Constraints(f,chr,p) :: cl2b clauses @ blocks)
            [] macros types tabbrs modes locals [] accs rest
      | Program.Namespace (loc, n) :: rest ->
          let p, locals1, chr1, rest = aux (n::ns) [] [] [] [] [] [] [] [] StrSet.empty rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside a namespace block";
          if locals1 <> [] then
            error "locals cannot be declared inside a namespace block";
          aux_end_block loc ns (Namespace (n,p) :: cl2b clauses @ blocks)
            [] macros types tabbrs modes locals chr accs rest
      | Program.Shorten (loc,[]) :: _ ->
          anomaly ~loc "parser returns empty list of shorten directives"
      | Program.Shorten (loc,directives) :: rest ->
          let shorthand (full_name,short_name) = { iloc = loc; full_name; short_name } in
          let shorthands = List.map shorthand directives in
          let p, locals1, chr1, rest = aux ns [] [] [] [] [] [] [] [] accs rest in
          if locals1 <> [] then
            error "locals cannot be declared after a shorthand";
          if chr1 <> [] then
            error "CHR cannot be declared after a shorthand";
          aux ns ((Shorten(shorthands,p) :: cl2b clauses @ blocks))
            [] macros types tabbrs modes locals chr accs rest

      | Program.Accumulated (_,[]) :: rest ->
          aux ns blocks clauses macros types tabbrs modes locals chr accs rest

      | Program.Accumulated (loc,(digest,a) :: more) :: rest ->
          let rest = Program.Accumulated (loc, more) :: rest in
          let digest = String.concat "." (digest :: List.map F.show ns) in
          if StrSet.mem digest accs then
            aux ns blocks clauses macros types tabbrs modes locals chr accs rest
          else
            aux ns blocks clauses macros types tabbrs modes locals chr
              (StrSet.add digest accs)
              (Program.Begin loc :: a @ Program.End loc :: rest)

      | Program.Clause c :: rest ->
          let c = structure_clause_attributes c in
          aux ns blocks (c::clauses) macros types tabbrs modes locals chr accs rest
      | Program.Macro m :: rest ->
          aux ns blocks clauses (m::macros) types tabbrs modes locals chr accs rest
      | Program.Pred (t,m) :: rest ->
          aux ns blocks clauses macros types tabbrs modes locals chr accs
            (Program.Mode [m] :: Program.Type [t] :: rest)
      | Program.Mode ms :: rest ->
          aux ns blocks clauses macros types tabbrs (ms @ modes) locals chr accs rest
      | Program.Type [] :: rest ->
          aux ns blocks clauses macros types tabbrs modes locals chr accs rest
      | Program.Type (t::ts) :: rest ->
          let t = structure_type_attributes t in
          let types = if List.mem t types then types else t :: types in
          aux ns blocks clauses macros types tabbrs modes locals chr accs
            (Program.Type ts :: rest)
      | Program.TypeAbbreviation abbr :: rest ->
          aux ns blocks clauses macros types (abbr :: tabbrs) modes locals chr accs rest
      | Program.Local l :: rest ->
          aux ns blocks clauses macros types tabbrs modes (l@locals) chr accs rest
      | Program.Chr r :: rest ->
          let r = structure_chr_attributes r in
          aux ns blocks clauses macros types tabbrs modes locals (r::chr) accs rest

    and aux_end_block loc ns blocks clauses macros types tabbrs modes locals chr accs rest =
      match rest with
      | Program.End _ :: rest ->
          aux ns blocks clauses macros types tabbrs modes locals chr accs rest
      | _ -> error ~loc "matching } is missing"

    in
    let blocks, locals, chr, rest = aux [] [] [] [] [] [] [] [] [] StrSet.empty dl in
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

  type quotation = depth:int -> State.t -> Loc.t -> string -> State.t * term
  let named_quotations = ref StrMap.empty
  let default_quotation = ref None
  
  let set_default_quotation f = default_quotation := Some f
  let register_named_quotation ~name:n f =
    named_quotations := StrMap.add n f !named_quotations

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

  let singlequote = ref None
  let backtick = ref None

  let declare_singlequote_compilation name f =
    match !singlequote with
    | None -> singlequote := Some(name,f)
    | Some(oldname,_) ->
         error("Only one custom compilation of 'ident' is supported. Current: "
           ^ oldname ^ ", new: " ^ name)
  let declare_backtick_compilation name f =
    match !backtick with
    | None -> backtick := Some(name,f)
    | Some(oldname,_) ->
         error("Only one custom compilation of `ident` is supported. Current: "
           ^ oldname ^ ", new: " ^ name)

  let compile_singlequote state x =
    match !singlequote with
    | None -> let state, (_,t) = Symbols.allocate_global_symbol state x in state, t
    | Some(_,f) -> f state x
  let compile_backtick state x =
    match !backtick with
    | None -> let state, (_,t) = Symbols.allocate_global_symbol state x in state, t
    | Some(_,f) -> f state x

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
  val merge_types :
    Structured.typ list ->
    Structured.typ list ->
    Structured.typ list
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
  val lp : quotation
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
    State.declare ~name:"elpi:argmap" ~pp:(todopp "elpi:argmap")
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
    State.declare ~name:"elpi:varmap" ~pp:(todopp "elpi:varmap")
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
    State.declare ~name:"elpi:mtm" ~pp:(todopp "elpi:mtm")
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

let preterm_of_ast ?(on_type=false) loc ~depth:arg_lvl macro state ast =

  let spilling = ref false in
  let spy_spill c =
    spilling := !spilling || c == D.Global_symbols.spillc in

  let is_uvar_name f = 
     let c = (F.show f).[0] in
     ('A' <= c && c <= 'Z') in
    
  let is_discard f =
    F.(equal f dummyname) ||
    let c = (F.show f).[0] in
     c = '_' in

  let is_macro_name f =
     let c = (F.show f).[0] in
     c = '@' in

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
    if on_type then error ~loc ("Macros cannot occur in types. Use a typeabbrev declaration instead");
    try aux lvl state (fst (F.Map.find f macro))
    with Not_found -> error ~loc ("Undeclared macro " ^ F.show f)

  (* compilation of "functors" *) 
  and stack_funct_of_ast curlvl state f =
    try state, F.Map.find f (get_varmap state)
    with Not_found ->
     if is_discard f then
       state, Discard
     else if is_uvar_name f then
       mk_Arg state ~name:(F.show f) ~args:[]
     else if is_macro_name f then
       stack_macro_of_ast curlvl state f
     else if not on_type && Builtins.is_declared_str state (F.show f) then
       state, Builtin(fst(Symbols.get_global_symbol state f),[])
     else if CustomFunctorCompilation.is_backtick f then
       CustomFunctorCompilation.compile_backtick state f
     else if CustomFunctorCompilation.is_singlequote f then
       CustomFunctorCompilation.compile_singlequote state f
     else
       let state, (_,t) = Symbols.allocate_global_symbol state f in
       state, t

  and aux lvl state = function
    | Ast.Term.Const f when F.(equal f nilf) -> state, Term.Nil
    | Ast.Term.Const f -> stack_funct_of_ast lvl state f
    | Ast.Term.App(Ast.Term.Const f, [hd;tl]) when F.(equal f consf) ->
       let state, hd = aux lvl state hd in
       let state, tl = aux lvl state tl in
       state, Term.Cons(hd,tl)
    | Ast.Term.App(Ast.Term.Const f, tl) ->
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
    | Ast.Term.App (Ast.Term.App (f,l1),l2) ->
       aux lvl state (Ast.Term.App (f, l1@l2))
    | Ast.Term.CData c -> state, Term.CData (CData.hcons c)
    | Ast.Term.App (Ast.Term.Lam _,_) ->
        error ~loc "Beta-redexes not allowed, use something like (F = x\\x, F a)"
    | Ast.Term.App (Ast.Term.CData _,_) ->
        error ~loc "Applied literal"
    | Ast.Term.Quoted { Ast.Term.data; kind = None; loc } ->
         let unquote =
           option_get ~err:"No default quotation" !default_quotation in
         let state = set_mtm state (Some { macros = macro}) in
         begin try
           let state, t = unquote ~depth:lvl state loc data in
           hcons_alien_term state t
         with Elpi_parser.Parser_config.ParseError(loc,msg) -> error ~loc msg end
    | Ast.Term.Quoted { Ast.Term.data; kind = Some name; loc } ->
         let unquote =
           try StrMap.find name !named_quotations
           with Not_found -> anomaly ("No '"^name^"' quotation") in
         let state = set_mtm state (Some { macros = macro}) in
         begin try
           let state, t = unquote ~depth:lvl state loc data in
           hcons_alien_term state t
         with Elpi_parser.Parser_config.ParseError(loc,msg) -> error ~loc msg end
    | Ast.Term.App (Ast.Term.Quoted _,_) ->
        error ~loc "Applied quotation"
  in

  (* arg_lvl is the number of local variables *)
  let state, t = aux arg_lvl state ast in
  state, t, !spilling
;;

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
let preterms_of_ast ?on_type loc ~depth macros state f t =
  assert(is_empty_amap (get_argmap state));
  let state, term, spilling = preterm_of_ast ?on_type loc ~depth macros state t in
  let state, terms = f ~depth state term in
  let amap = get_argmap state in
  let state = State.end_clause_compilation state in
  (* TODO: may have spurious entries in the amap *)
  state, List.map (fun (loc,term) -> { term; amap; loc; spilling }) terms
;;

(* exported *)
let query_preterm_of_function ~depth:_ macros state f =
  assert(is_empty_amap (get_argmap state));
  let state = set_mtm state (Some { macros }) in
  let state, (loc, main), gls = f state in
  let state, gls = !Data.Conversion.extra_goals_postprocessing gls state in
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

  let compile_type_abbrev lcs state { Ast.TypeAbbreviation.name; nparams; loc; value } =
    let state, (taname, _) = Symbols.allocate_global_symbol state name in
    let state, tavalue = preterms_of_ast ~on_type:true loc ~depth:lcs F.Map.empty state (fun ~depth:_ state x -> state, [loc,x]) value in
    let tavalue = assert(List.length tavalue = 1); List.hd tavalue in
    if tavalue.amap.nargs != 0 then
      error ~loc ("type abbreviation for " ^ F.show name ^ " has unbound variables");
    state, { taname; tavalue; taparams = nparams; taloc = loc }

  let add_to_index_type_abbrev state m ({ taname; taloc; tavalue; taparams } as x) =
    if C.Map.mem taname m then begin
      let { taloc = otherloc; tavalue = othervalue; taparams = otherparams } =
        C.Map.find taname m in
      if taparams != otherparams || othervalue.term != tavalue.term then
      error ~loc:taloc
        ("duplicate type abbreviation for " ^ Symbols.show state taname ^
          ". Previous declaration: " ^ Loc.show otherloc)
    end;
    C.Map.add taname x m

  let compile_type lcs state { Ast.Type.attributes; loc; name; ty } =
    let state, (tname, _) = Symbols.allocate_global_symbol state name in
    let state, ttype =
      preterms_of_ast ~on_type:true loc ~depth:lcs F.Map.empty state (fun ~depth:_ state x -> state, [loc,x]) ty in
    let ttype = assert(List.length ttype = 1); List.hd ttype in
    state, { Structured.tindex = attributes; decl = { tname; ttype; tloc = loc } }

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

  let compile_mode (state, modes) { Ast.Mode.name; args; loc } =
    let state, mname = funct_of_ast state name in
    check_duplicate_mode state mname (args,loc) modes;
    state, C.Map.add mname (args,loc) modes

  let merge_modes state m1 m2 =
    C.Map.fold (fun k v m ->
      check_duplicate_mode state k v m;
      C.Map.add k v m)
    m2 m1

  let merge_types t1 t2 =
    t1 @ (List.filter (fun x -> not @@ List.mem x t1) t2)

  let merge_type_abbrevs s m1 m2 =
    C.Map.fold (fun _ v m -> add_to_index_type_abbrev s m v) m1 m2

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
    List.fold_left (fun s { Structured.decl = { tname } } ->
        C.Set.add tname s)
      C.Set.empty types

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


  let run (state : State.t) ~toplevel_macros p =
 (* FIXME: otypes omodes - NO, rewrite spilling on data.term *)
    let rec compile_program omacros lcs state { macros; types; type_abbrevs; modes; body } =
      check_no_overlap_macros omacros macros;
      let active_macros =
        List.fold_left compile_macro omacros macros in
      let state, type_abbrevs = map_acc (compile_type_abbrev lcs) state type_abbrevs in
      let type_abbrevs = List.fold_left (add_to_index_type_abbrev state) C.Map.empty type_abbrevs in
      let state, types =
        map_acc (compile_type lcs) state types in
      let state, modes = List.fold_left compile_mode (state,C.Map.empty) modes in
      let defs_m = defs_of_modes modes in
      let defs_t = defs_of_types types in
      let defs_ta = defs_of_type_abbrevs type_abbrevs in
      let lcs, state, types, type_abbrevs, modes, defs_b, body =
        compile_body active_macros types type_abbrevs modes lcs C.Set.empty state body in
      let symbols = C.Set.(union (union (union defs_m defs_t) defs_b) defs_ta) in
      (state : State.t), lcs, active_macros,
      { Structured.types; type_abbrevs; modes; body; symbols }

    and compile_body macros types type_abbrevs modes lcs defs state = function
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
          let types = merge_types types tp in
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
      | Constraints (clique, rules, p) :: rest ->
          (* XXX missing check for nested constraints *)
          let state, clique = map_acc funct_of_ast state clique in
          let state, rules =
            map_acc (prechr_rule_of_ast lcs macros) state rules in
          let state, lcs, _, p = compile_program macros lcs state p in
          let lcs, state, types, type_abbrevs, modes, defs, compiled_rest =
            compile_body macros types type_abbrevs modes lcs defs state rest in
          lcs, state, types, type_abbrevs, modes,
          C.Set.union defs p.Structured.symbols,
          Structured.Constraints(clique, rules,p) :: compiled_rest
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

  val run : State.t -> Structured.program -> Flat.program

  val relocate : State.t -> D.constant D.Constants.Map.t -> Flat.program  -> Flat.program

end = struct (* {{{ *)


  open Structured

  (* This function *must* re-hashcons all leaves (Const) and recognize
     builtins since it is (also) used to apply a compilation unit relocation *)

  let smart_map_term ?(on_type=false) state f t =
    let rec aux = function
      | Const c ->
          let c1 = f c in
          if not on_type && Builtins.is_declared state c1 then Builtin(c1,[])
          else Symbols.get_canonical state c1
      | Lam t as x ->
          let t1 = aux t in
          if t == t1 then x else Lam t1
      | AppArg(i,ts) as x ->
          let ts1 = smart_map aux ts in
          if ts == ts1 then x else AppArg(i,ts1)
      | AppUVar(r,lvl,ts) as x ->
          assert(!!r == D.dummy);
          let ts1 = smart_map aux ts in
          if ts == ts1 then x else AppUVar(r,lvl,ts1)
      | Builtin(c,ts) ->
          let c1 = f c in
          let ts1 = smart_map aux ts in
          if not on_type && Builtins.is_declared state c1 then Builtin(c,ts1)
          else if ts1 = [] then Symbols.get_canonical state c1 else App(c,List.hd ts1,List.tl ts1)
      | App(c,t,ts) ->
          let c1 = f c in
          let t1 = aux t in
          let ts1 = smart_map aux ts in
          if not on_type && Builtins.is_declared state c1 then Builtin (c1,t1 :: ts1)
          else App(c1,t1,ts1)
      | Cons(hd,tl) as x ->
          let hd1 = aux hd in
          let tl1 = aux tl in
          if hd == hd1 && tl == tl1 then x else Cons(hd1,tl1)
      | UVar(r,_,_) as x ->
          assert(!!r == D.dummy);
          x
      | (Arg _ | CData _ | Nil | Discard) as x -> x
    in
      aux t

let subst_amap state f { nargs; c2i; i2n; n2t; n2i } =
  let c2i = Constants.Map.fold (fun k v m -> Constants.Map.add (f k) v m) c2i Constants.Map.empty in
  let n2t = StrMap.map (fun (t,c) ->
    let c = f c in
    let t = match t with
      | Const c -> Symbols.get_canonical state (f c)
      | _ -> assert false in
    t,c) n2t in
  { nargs; c2i; i2n; n2t; n2i }

  let smart_map_type state f ({ Structured.tindex; decl = { tname; ttype; tloc }} as tdecl) =
    let tname1 = f tname in
    let ttype1 = smart_map_term ~on_type:true state f ttype.term in
    let tamap1 =subst_amap state f ttype.amap in
    if tname1 == tname && ttype1 == ttype.term && ttype.amap = tamap1 then tdecl
    else { Structured.tindex; decl = { tname = tname1; tloc; ttype = { term = ttype1; amap = tamap1; loc = ttype.loc; spilling = ttype.spilling } } }


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

  let smart_map_preterm ?on_type state f ({ term; amap; loc; spilling } as x) =
    let term1 = smart_map_term ?on_type state f term in
    let amap1 = subst_amap state f amap in
    if term1 == term && amap1 == amap then x
    else { term = term1; amap = amap1; loc; spilling }

  let map_clause state f ({ Ast.Clause.body } as x) =
    { x with Ast.Clause.body = smart_map_preterm state f body }

  let map_pair f g (x,y) = f x, g y

  type subst = (string list * C.t C.Map.t)


  let apply_subst (f : C.t C.Map.t -> 'a -> 'a) (s : subst) : 'a -> 'a =
    fun x -> f (snd s) x

  let _apply_subst_list f = apply_subst (fun x -> smart_map (f x))

  let tabbrevs_map state f m =
    C.Map.fold (fun _ { taname; tavalue; taparams; taloc } m ->
      (* TODO: check for collisions *)
      let taname = f taname in
      let tavalue = smart_map_preterm ~on_type:true state f tavalue in
      C.Map.add taname { taname; tavalue; taparams; taloc } m
      ) m C.Map.empty

  let apply_subst_constant ?live_symbols =
    apply_subst (fun m x ->
      let x = try C.Map.find x m with Not_found -> x in
      begin match live_symbols with None -> () | Some r -> r := C.Set.add x !r end;
      x)

  let apply_subst_types ?live_symbols st s = smart_map (smart_map_type st (apply_subst_constant ?live_symbols s))

  let apply_subst_type_abbrevs ?live_symbols st s = tabbrevs_map st (apply_subst_constant ?live_symbols s)

  let apply_subst_modes ?live_symbols s m =
    C.Map.fold (fun c v m -> C.Map.add (apply_subst_constant ?live_symbols s c) v m) m C.Map.empty

  let apply_subst_chr ?live_symbols st s l =
    map_pair (smart_map (apply_subst_constant ?live_symbols s))
             (smart_map (map_chr st (apply_subst_constant ?live_symbols s))) l

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
        let types = ToDBL.merge_types (apply_subst_types ~live_symbols state insubst t) types in
        let type_abbrevs = ToDBL.merge_type_abbrevs state (apply_subst_type_abbrevs ~live_symbols state insubst ta) type_abbrevs in
        let modes = ToDBL.merge_modes state (apply_subst_modes ~live_symbols insubst m) modes in
        let types, type_abbrevs, modes, clauses, chr =
          compile_body live_symbols state lcs types type_abbrevs modes clauses chr insubst body in
        compile_body live_symbols state lcs types type_abbrevs modes clauses chr subst rest
    | Namespace (extra, { types = t; type_abbrevs = ta; modes = m; body; symbols = s }) :: rest ->
        let state, insubst = push_subst state extra s subst in
        let types = ToDBL.merge_types (apply_subst_types ~live_symbols state insubst t) types in
        let type_abbrevs = ToDBL.merge_type_abbrevs state (apply_subst_type_abbrevs ~live_symbols state insubst ta) type_abbrevs in
        let modes = ToDBL.merge_modes state (apply_subst_modes ~live_symbols insubst m) modes in
        let types, type_abbrevs, modes, clauses, chr =
          compile_body live_symbols state lcs types type_abbrevs modes clauses chr insubst body in
        compile_body live_symbols state lcs types type_abbrevs modes clauses chr subst rest
    | Clauses cl :: rest ->
        let cl = apply_subst_clauses ~live_symbols state subst cl in
        let clauses = clauses @ cl in
        compile_body live_symbols state lcs types type_abbrevs modes clauses chr subst rest
    | Constraints (clique, rules, { types = t; type_abbrevs = ta; modes = m; body }) :: rest ->
        let types = ToDBL.merge_types (apply_subst_types ~live_symbols state subst t) types in
        let type_abbrevs = ToDBL.merge_type_abbrevs state (apply_subst_type_abbrevs ~live_symbols state subst ta) type_abbrevs in
        let modes = ToDBL.merge_modes state (apply_subst_modes ~live_symbols subst m) modes in
        let chr = apply_subst_chr ~live_symbols state subst (clique,rules) :: chr in
        let types, type_abbrevs, modes, clauses, chr =
          compile_body live_symbols state lcs types type_abbrevs modes clauses chr subst body in
        compile_body live_symbols state lcs types type_abbrevs modes clauses chr subst rest

  let run state
    { Structured.local_names;
      pbody = { types; type_abbrevs; modes; body; symbols = _ };
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
    { Flat.types;
      type_abbrevs;
      modes;
      clauses;
      chr = List.rev chr;
      local_names;
      toplevel_macros;
      symbols = !live_symbols
    }

    let relocate state f {
      Flat.types;
      type_abbrevs;
      modes;
      clauses;
      chr;
      local_names;
      toplevel_macros;
      symbols;
    } =
      let f = [], f in
    {
      Flat.types = apply_subst_types state f types;
      type_abbrevs = apply_subst_type_abbrevs state f type_abbrevs;
      modes = apply_subst_modes f modes;
      clauses = apply_subst_clauses state f clauses;
      chr = smart_map (apply_subst_chr state f) chr;
      local_names;
      toplevel_macros;
      symbols;
    }



end (* }}} *)

module Spill : sig

  (* Eliminate {func call} *)

  val run : State.t -> Assembled.program -> Assembled.program

  (* Exported to compile the query *)
  val spill_preterm :
    State.t -> Structured.typ list -> (C.t -> mode) -> preterm -> preterm

end = struct (* {{{ *)

  let rec read_ty = function
    | App(c,x,[y]) when c == D.Global_symbols.variadic -> `Variadic (read_ty x,read_ty y)
    | App(c,x,[y]) when c == D.Global_symbols.arrowc -> 
        let ty_x = read_ty x in
        begin match read_ty y with
        | `Arrow(tys,ty) -> `Arrow (ty_x :: tys, ty)
        | ty -> `Arrow([ty_x], ty) end
    | Const x when x == D.Global_symbols.propc -> `Prop
    | _ -> `Unknown

  let type_of_const types c =
    try
      let { Structured.decl = { ttype } } =
        List.find (fun { Structured.decl = { tname } } -> tname == c) types in
      read_ty ttype.term
    with
      Not_found -> `Unknown

  let missing_args_of state loc modes types t =
    let c, args =
      let rec aux = function
        | App (c,_,[x]) when c == D.Global_symbols.implc -> aux x
        | App (c,x,xs) when c == D.Global_symbols.andc ->
            aux List.(hd (rev (x :: xs)))
        | App (c,x,xs) -> c, x :: xs
        | Const c -> c, []
        | Builtin(c,args) -> c, args
        | _ -> error ~loc "Only applications can be spilled"
      in
        aux t in
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
            let rec aux = function false :: l -> 1 + aux l | _ -> 0 in
            aux (List.rev mode) in
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
      let rec aux vars n =
        if n == 0 then []
        else begin
          incr spilled;
          mkApp (mk_Arg ("Spilled_" ^ string_of_int !spilled)) vars ::
            aux vars (n-1)
        end in
      fun vars n -> List.rev (aux vars n) in

    let mkAppSpilled fcall args =
      let rec on_last f = function
        | [] -> assert false
        | [x] -> [f x]
        | x::xs -> x :: on_last f xs
      in
      let rec aux = function
        | App(c,x,[y]) when c == D.Global_symbols.implc ->
            mkAppC c [x;aux y]
        | App (c,x,xs) when c == D.Global_symbols.andc ->
            mkAppC c (on_last aux (x::xs))
        | t -> mkApp t args
      in
        aux fcall in

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
           let rec aux ty args = match ty, args with
             | (`Variadic(_,`Prop) | `Arrow([],`Prop)), [] -> [],[],true
             | _, [] -> [],[],false
             | `Variadic(`Prop,_), a1 :: an ->
                   ([],spaux1_prop ctx a1) @@@ aux ty an
             | `Arrow(`Prop :: ty,c), a1 :: an ->
                   ([],spaux1_prop ctx a1) @@@ aux (`Arrow(ty,c)) an
             | `Arrow((_ :: _ as ty),c), a1 :: an ->
                   let spills, a1 = spaux ctx a1 in
                   let ty = drop (size_outermost_spill spills ~default:1) ty in
                   (spills, a1) @@@ aux (`Arrow(ty,c)) an
             | _, a1 :: an -> spaux ctx a1 @@@ aux ty an
           in
             aux (type_of_const types hd) args in
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

  let spill_chr state modes types (clique, rules) =
    let rules = List.map (spill_rule state modes types) rules in
    (clique, rules)

  let spill_clause state modes types ({ Ast.Clause.body = { term; amap; loc; spilling } } as x) =
    if not spilling then x
    else
      let amap, term = spill_term state loc modes types amap term in
      { x with Ast.Clause.body = { term; amap; loc; spilling = false } }

  let run state ({ Assembled.clauses; modes; types; chr } as p) =
    let clauses = List.map (spill_clause state (fun c -> fst @@ C.Map.find c modes) types) clauses in
    let chr = List.map (spill_chr state (fun c -> fst @@ C.Map.find c modes) types) chr in
    { p with Assembled.clauses; chr }

  let spill_preterm state types modes ({ term; amap; loc; spilling } as x) =
    if not spilling then x
    else
      let amap, term = spill_term state loc modes types amap term in
      { amap; term; loc; spilling = false; }

end (* }}} *)

(* This is marshalable *)

module Assemble : sig

  val assemble : flags -> State.t -> Assembled.program -> compilation_unit list -> State.t * Assembled.program

end = struct (* {{{ *)

  let sort_insertion old l =
    let add s { Ast.Clause.attributes = { Assembled.id }; loc } =
      match id with
      | None -> s
      | Some n ->
          if StrMap.mem n s then
            error ~loc ("a clause named " ^ n ^
                   " already exists at " ^ Loc.show (StrMap.find n s))
          else
            StrMap.add n loc s in
    let compile_clause ({ Ast.Clause.attributes = { Ast.Structured.id }} as c) =
      { c with Ast.Clause.attributes = { Assembled.id }}
    in
    let rec insert loc_name c l =
      match l, loc_name with
      | [],_ -> error ~loc:c.Ast.Clause.loc ("unable to graft this clause: no clause named " ^
             match loc_name with
             | Ast.Structured.After x -> x
             | Ast.Structured.Before x -> x)
      | { Ast.Clause.attributes = { Assembled.id = Some n }} as x :: xs,
        Ast.Structured.After name when n = name ->
           c :: x :: xs
      | { Ast.Clause.attributes = { Assembled.id = Some n }} as x :: xs,
        Ast.Structured.Before name when n = name ->
           x :: c :: xs
      | x :: xs, _ -> x :: insert loc_name c xs in
    let rec aux seen acc = function
      | [] -> List.rev acc
      | { Ast.Clause.attributes = { Ast.Structured.insertion = Some i }} as x :: xs ->
          let x = compile_clause x in
          aux (add seen x) (insert i x acc) xs
      | x :: xs ->
          let x = compile_clause x in
          aux (add seen x) (x :: acc) xs
    in
    aux StrMap.empty (List.rev old) l

  (* let shift_pp fmt ({ Data.Constants.c2s},s,{ Data.Constants.c2s = c2s2 }) =
    Format.fprintf fmt "{{ @[<hov 2>";
    IntMap.iter (fun k v ->
      Format.fprintf fmt "(%s)%a ->@ (%s)%a;@ "
        (Hashtbl.find c2s k) Int.pp k (Hashtbl.find c2s2 v) Int.pp v) s;
    Format.fprintf fmt "@] }}" *)
  let clause_name { Ast.Clause.attributes = { Ast.Structured.ifexpr } } = ifexpr

let assemble flags state code  (ul : compilation_unit list) =

  let state, clauses_rev, types, type_abbrevs, modes, chr_rev =
    List.fold_left (fun (state, cl1, t1, ta1, m1, c1) ({ symbol_table; code }  as _u) ->
      let state, { Flat.clauses = cl2; types = t2; type_abbrevs = ta2; modes = m2; chr = c2; toplevel_macros = _ } =
        let state, shift = Symbols.build_shift ~flags ~base:state symbol_table in
        let code =
          if C.Map.is_empty shift then code
          else Flatten.relocate state shift code in
        state, code in
      let modes = ToDBL.merge_modes state m1 m2 in
      let type_abbrevs = ToDBL.merge_type_abbrevs state ta1 ta2 in
      let types = ToDBL.merge_types t1 t2 in
      let cl2 = filter_if flags clause_name cl2 in
      state, cl2 :: cl1, types, type_abbrevs, modes, c2 :: c1
    ) (state, [], code.Assembled.types, code.Assembled.type_abbrevs, code.Assembled.modes, []) ul in
  let clauses = List.concat (List.rev clauses_rev) in
  let clauses = sort_insertion code.clauses clauses in
  let chr = List.concat (code.Assembled.chr :: List.rev chr_rev) in
  let chr =
    let pifexpr { pifexpr } = pifexpr in
    List.map (fun (symbs,rules) -> symbs, filter_if flags pifexpr rules) chr in
  state, { Assembled.clauses; types; type_abbrevs; modes; chr; local_names = code.Assembled.local_names; toplevel_macros = code.Assembled.toplevel_macros }

end (* }}} *)


(****************************************************************************
  API
 ****************************************************************************)

let w_symbol_table s f x =
  let table = Symbols.compile_table @@ State.get Symbols.table s in
  let pp_ctx = { table; uv_names = ref (IntMap.empty,0) } in
  Util.set_spaghetti_printer Data.pp_const (R.Pp.pp_constant ~pp_ctx);
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

  let p = Flatten.run s p in

  if print_passes then
    Format.eprintf "== Flat ================@\n@[<v 0>%a@]@\n"
      (w_symbol_table s Flat.pp_program) p;

  s, {
    version = "%%VERSION_NUM%%";
    code = p;
    symbol_table = Symbols.prune (State.get Symbols.table s) p.Flat.symbols
  }
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

let header_of_ast ~flags ~parser:p builtins ast : header =
  let state = D.State.init () in
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
  let state = D.State.set parser state (Some p) in
  let state, u = unit_or_header_of_ast flags state ast in
  print_unit flags u;
  state, u

let unit_of_ast ~flags ~header:(s, (header : compilation_unit)) p : compilation_unit =
  let toplevel_macros = header.code.Flat.toplevel_macros in
  let _, u = unit_or_header_of_ast flags s ~toplevel_macros p in
  print_unit flags u;
  u

let assemble_units ~flags ~header:(s,h) units : program =

  let nunits_with_locals =
    (h :: units) |> List.filter (fun {code = { Flat.local_names = x }} -> x > 0) |> List.length in

  if nunits_with_locals > 0 then
    error "Only 1 compilation unit is supported when local directives are used";

  let init = { Assembled.empty with toplevel_macros = h.code.toplevel_macros; local_names = h.code.local_names } in

  let s, p = Assemble.assemble flags s init (h :: units) in

  let { print_passes } = flags in

  if print_passes then
    Format.eprintf "== Assembled ================@\n@[<v 0>%a@]@\n"
      (w_symbol_table s Assembled.pp_program) p;

  let p = Spill.run s p in

  if print_passes then
    Format.eprintf "== Spilled ================@\n@[<v 0>%a@]@\n"
      (w_symbol_table s Assembled.pp_program) p;

 s, p
;;

let append_units ~flags ~base:(s,p) units : program =
  let s, p = Assemble.assemble flags s p units in
  let { print_passes } = flags in

  if print_passes then
    Format.eprintf "== Assembled ================@\n@[<v 0>%a@]@\n"
      (w_symbol_table s Assembled.pp_program) p;

  let p = Spill.run s p in

  if print_passes then
    Format.eprintf "== Spilled ================@\n@[<v 0>%a@]@\n"
      (w_symbol_table s Assembled.pp_program) p;

  s, p

let program_of_ast ~flags ~header p : program =
  let u = unit_of_ast ~flags ~header p in
  assemble_units ~flags ~header [u]

let is_builtin state tname =
  Builtins.is_declared state tname

let check_all_builtin_are_typed state types =
   Constants.Set.iter (fun c ->
     if not (List.exists
        (fun { Structured.tindex; decl = { tname }} ->
            tindex = Ast.Structured.External && tname == c) types) then
       error ("Built-in without external type declaration: " ^ Symbols.show state c))
   (Builtins.all state);
  List.iter (fun { Structured.tindex; decl = { tname; tloc }} ->
    if tindex = Ast.Structured.External && not (is_builtin state tname) then
      error ~loc:tloc ("external type declaration without Built-in: " ^
            Symbols.show state tname))
  types
;;

let check_no_regular_types_for_builtins state types =
  List.iter (fun {Structured.tindex; decl = { tname; tloc } } ->
    if tindex <> Ast.Structured.External && is_builtin state tname then
      anomaly ~loc:tloc ("type declaration for Built-in " ^
            Symbols.show state tname ^ " must be flagged as external");
 ) types

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

let uvbodies_of_assignments assignments =
  (* Clients may add spurious args that, not occurring in the query,
     are not turned into uvars *)
   let assignments = assignments |> StrMap.filter (fun _ -> function
     | UVar _ | AppUVar _ -> true
     | _ -> false) in
   State.end_goal_compilation (StrMap.map (function
     | UVar(b,_,_) | AppUVar(b,_,_) -> b
     | _ -> assert false) assignments)

let query_of_ast (compiler_state, assembled_program) t =
  let compiler_state = State.begin_goal_compilation compiler_state in
  let initial_depth = assembled_program.Assembled.local_names in
  let types = assembled_program.Assembled.types in
  let type_abbrevs = assembled_program.Assembled.type_abbrevs in
  let modes = C.Map.map fst assembled_program.Assembled.modes in
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
    type_abbrevs;
    clauses = assembled_program.Assembled.clauses;
    chr = assembled_program.Assembled.chr;
    initial_depth;
    query;
    query_arguments = Query.N;
    initial_goal;
    assignments;
    compiler_state = state |> (uvbodies_of_assignments assignments);
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
    clauses = assembled_program.Assembled.clauses;
    chr = assembled_program.Assembled.chr;
    initial_depth;
    query;
    query_arguments = Query.N;
    initial_goal;
    assignments;
    compiler_state = state |> (uvbodies_of_assignments assignments);
  }


let query_of_data (state, p) loc (Query.Query { arguments } as descr) =
  let state = State.begin_goal_compilation state in
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
      }
;;

let compile_clause modes initial_depth state
    { Ast.Clause.body = ({ amap = { nargs }} as body); loc }
=
  let state, body = stack_term_of_preterm ~depth:0 state body in
  let cl, _, morelcs =
    try R.clausify1 ~loc modes ~nargs ~depth:initial_depth body
    with D.CannotDeclareClauseForBuiltin(loc,c) ->
      error ?loc ("Declaring a clause for built in predicate " ^ Symbols.show state c)
    in
  if morelcs <> 0 then error ~loc "sigma in a toplevel clause is not supported";
  state, cl

let chose_indexing state predicate l =
  let rec all_zero = function
    | [] -> true
    | 0 :: l -> all_zero l
    | _ -> false in
  let rec aux n = function
    | [] -> error ("Wrong indexing for " ^ Symbols.show state predicate)
    | 0 :: l -> aux (n+1) l
    | 1 :: l when all_zero l -> MapOn n
    | _ -> Hash l
  in
    aux 0 l

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
    clauses;
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
    List.fold_left (fun (state, chr) (clique, rules) ->
      let chr, clique = CHR.new_clique (Symbols.show state) clique chr in
      let state, rules = map_acc (compile_chr initial_depth) state rules in
      List.iter (check_rule_pattern_in_clique state clique) rules;
      state, List.fold_left (fun x y -> CHR.add_rule clique y x) chr rules)
    (state, CHR.empty) chr in
  let indexing =
    let add_indexing_for name tindex map =
      let mode = try C.Map.find name modes with Not_found -> [] in
      let declare_index, index =
        match tindex with
        | Some (Ast.Structured.Index l) -> true, chose_indexing state name l
        | _ -> false, chose_indexing state name [1] in
      try
        let _, old_tindex = C.Map.find name map in
        if old_tindex <> index then
          if old_tindex <> MapOn 1 && declare_index then
            error ("multiple and inconsistent indexing attributes for " ^
                      Symbols.show state name)
          else
            if declare_index then C.Map.add name (mode,index) map
            else map
        else
          map
      with Not_found ->
        C.Map.add name (mode,index) map in
    let map = List.fold_left (fun acc { Structured.decl = { tname }; tindex} -> add_indexing_for tname (Some tindex) acc) C.Map.empty types in
    let map = C.Map.fold (fun k _ m -> add_indexing_for k None m) modes map in
    map in
  let state, clauses =
    map_acc (compile_clause modes initial_depth) state clauses in
  let prolog_program = R.make_index ~depth:initial_depth ~indexing clauses in
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
    D.compiled_program = prolog_program;
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

let pp_query pp fmt {
    WithMain.clauses;
    initial_depth;
    compiler_state;
    query; } =
  let pp_ctx = {
    uv_names = ref (IntMap.empty, 0);
    table = Symbols.compile_table (State.get Symbols.table compiler_state);
  } in
  Format.fprintf fmt "@[<v>";
  List.iter (fun { Ast.Clause.body } ->
    Format.fprintf fmt "%a.@;" (pp ~pp_ctx ~depth:initial_depth)
      (snd(stack_term_of_preterm compiler_state ~depth:initial_depth body)))
  clauses;
  Format.fprintf fmt "?- %a.@;" (pp ~pp_ctx ~depth:initial_depth)
    (snd (stack_term_of_preterm compiler_state ~depth:initial_depth query));
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

let quote_preterm time ~compiler_state new_state ?(on_type=false) { term; amap } =
  let new_state = ref new_state in
  let mkQApp = mkQApp ~on_type in
  let mkQCon c =
    let n, x = mkQCon time ~compiler_state !new_state ~on_type ~amap c in
    new_state := n;
    x in
  let rec aux depth term = match term with
    | App(c,CData s,[])
      when on_type && c == D.Global_symbols.ctypec && D.C.is_string s -> term
    | App(c,s,[t]) when on_type && c == D.Global_symbols.arrowc ->
        App(arrowc,aux depth s,[aux depth t])
    | Const n when on_type && Symbols.show compiler_state n = "prop" -> term

    | Const n -> mkQCon n
    | Builtin(c,[]) -> mkQCon c
    | Lam x -> App(lamc,Lam (aux (depth+1) x),[])
    | App(c,x,xs) ->
        mkQApp (mkQCon c :: List.(map (aux depth) (x :: xs)))
    | Builtin(c,args) -> mkQApp (mkQCon c :: List.map (aux depth) args)

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
    | Cons(hd,tl) -> mkQApp [mkQCon D.Global_symbols.consc; aux depth hd; aux depth tl]
    | Nil -> mkQCon D.Global_symbols.nilc
    | Discard -> mkQCon discardc
  in
  let term = aux amap.nargs term in
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
  let new_state, clist = map_acc (quote_clause time ~compiler_state) new_state clauses in
  let new_state, queryt = quote_preterm time ~on_type:false ~compiler_state new_state query in
  let q =
    App(clausec,CData (quote_loc ~id:"query" query.loc),
      [R.list_to_lp_list names;
       close_w_binder argc queryt query.amap]) in
  new_state, clist, q

let unfold_type_abbrevs ~compiler_state lcs type_abbrevs { term; loc; amap } =
  let find_opt c =
    try Some (C.Map.find c type_abbrevs) with Not_found -> None in
  let rec aux seen = function
    | Const c as x ->
        begin match find_opt c with
        | Some { tavalue; taparams } ->
          if taparams > 0 then
            error ~loc ("type abbreviation " ^ Symbols.show compiler_state c ^ " needs " ^
              string_of_int taparams ^ " arguments");
          if C.Set.mem c seen then
            error ~loc
              ("looping while unfolding type abbreviation for "^ Symbols.show compiler_state c);
          aux (C.Set.add c seen) tavalue.term
        | None -> x
        end
    | App(c,t,ts) as x ->
        begin match find_opt c with
        | Some { tavalue; taparams } ->
          let nargs = 1 + List.length ts in
          if taparams > nargs then
            error ~loc ("type abbreviation " ^ Symbols.show compiler_state c ^ " needs " ^
              string_of_int taparams ^ " arguments, only " ^
              string_of_int nargs ^ " are provided");
          if C.Set.mem c seen then
            error ~loc
              ("looping while unfolding type abbreviation for "^ Symbols.show compiler_state c);
          aux (C.Set.add c seen) (R.deref_appuv ~from:lcs ~to_:lcs (t::ts) tavalue.term)
        | None ->
          let t1 = aux seen t in
          let ts1 = smart_map (aux seen) ts in
          if t1 == t && ts1 == ts then x
          else App(c,t1,ts1)
        end
    | x -> x
  in
    { term = aux C.Set.empty term; loc; amap; spilling = false }

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
  ({ WithMain.types; type_abbrevs; initial_depth; compiler_state } as q) =
  let time = `Compiletime in
  let state, p,q = quote_syntax time state q in
  let state, tlist = map_acc
    (fun state { Structured.decl = { tname; ttype } } ->
      let state, c = mkQCon time ~compiler_state state ~on_type:false tname in
      let ttypet = unfold_type_abbrevs ~compiler_state initial_depth type_abbrevs ttype in
      let state, ttypet = quote_preterm time ~compiler_state state ~on_type:true ttypet in
      state, App(colonc,c, [close_w_binder forallc ttypet ttype.amap]))
      state types in
  let state, talist =
    C.Map.bindings type_abbrevs |>
    map_acc (fun state (name, { tavalue;  } ) ->
      let tavaluet = unfold_type_abbrevs ~compiler_state initial_depth type_abbrevs tavalue in
      let state, tavaluet = quote_preterm time ~compiler_state state ~on_type:true tavaluet in
      state, App(colonec, D.C.of_string (Symbols.show compiler_state name), [lam2forall tavaluet])) state
    in
  let loc = Loc.initial "(static_check)" in
  let query =
    query_of_term (state, program) (fun ~depth state ->
      assert(depth=0);
      state, (loc,App(checkc,R.list_to_lp_list p,[q;R.list_to_lp_list tlist;R.list_to_lp_list talist])), []) in
  let executable = optimize_query query in
  exec executable <> Failure
;;

