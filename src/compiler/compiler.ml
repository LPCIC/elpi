(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_parser
open Elpi_runtime

open Util
module F = Ast.Func
module R = Runtime_trace_off
module D = Data

let elpi_language = Compiler_data.elpi_language

type flags = {
  defined_variables : StrSet.t;
  print_units : bool;
  time_typechecking : bool;
}
[@@deriving show]

let default_flags = {
  defined_variables = StrSet.empty;
  print_units = false;
  time_typechecking = false;
}

let parser : (module Parse.Parser) option D.State.component = D.State.declare
  ~descriptor:D.elpi_state_descriptor
  ~name:"elpi:parser"
  ~pp:(fun fmt _ -> Format.fprintf fmt "<parser>")
  ~clause_compilation_is_over:(fun x -> x)
  ~compilation_is_over:(fun x -> Some x)
  ~execution_is_over:(fun _ -> None)
  ~init:(fun () -> None)
  ()

let filter1_if { defined_variables } proj c =
  match proj c with
  | None -> true
  | Some e when StrSet.mem e defined_variables -> true
  | Some _ -> false

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
  type table [@@deriving show]

  val pp_table : Format.formatter -> table -> unit
  val equal_globals : table -> table -> bool
  (* val diff : table -> table -> table *)

  val empty : unit -> table
  val allocate_global_symbol     : D.State.t -> table -> D.Symbol.t -> table * (constant * D.term)
  val allocate_bound_symbol      : D.State.t -> table -> constant -> table * D.term
  val get_global_symbol          : table -> D.Symbol.t -> constant option
  val get_canonical              : D.State.t -> table -> constant -> D.term
  val global_name : D.State.t -> table -> constant -> F.t
  val compile : table -> D.symbol_table
  val compile_s2c : table -> (constant * D.term) D.Symbol.RawMap.t

end = struct
  open Compiler_data

  type table = {
    ast2ct : (constant * D.term) D.Symbol.RawMap.t;
    c2t : D.term Constants.Map.t;
    c2s : Symbol.t Constants.Map.t;
    last_global : int;
  }
  [@@deriving show]

  let equal_globals m1 m2 = m1.last_global = m2.last_global


  (* let diff big small =
    Util.Constants.Map.fold (fun c s m ->
      { m with c2s = Util.Constants.Map.remove c m.c2s; c2t = Util.Constants.Map.remove c m.c2t; ast2ct = .Map.remove (F.from_string s) m.ast2ct}
      ) small.c2s big *)

  let compile { last_global; c2t; c2s; ast2ct } =
    let t = { D.c2s; c2t = Hashtbl.create (Util.Constants.Map.cardinal c2t); frozen_constants = last_global; } in
  (* We could compile the Map c2t to a Hash table upfront, but there is no need
     since it is extended at run time anyway *)
  (* Symbol.RawMap.iter (fun k (c,v) -> lrt c = c Hashtbl.add t.c2t c v; Hashtbl.add t.c2s c (F.show k)) ast2ct; *)
    t
    
  let compile_s2c { ast2ct } = ast2ct

  let allocate_global_symbol_aux (x:D.Symbol.t) ({ c2t; c2s; ast2ct; last_global } as table) =
    try table, D.Symbol.RawMap.find x ast2ct
    with Not_found ->
      (* Format.eprintf "NEW %a -> %d\n" Symbol.pp x last_global; *)
      let last_global = last_global - 1 in
      let n = last_global in
      let xx = D.Term.Const n in
      let p = n,xx in
      let c2t = Util.Constants.Map.add n xx c2t in
      let ast2ct = D.Symbol.RawMap.add x p ast2ct in
      let c2s = Util.Constants.Map.add n x c2s in
      { c2t; c2s; ast2ct; last_global }, p

  let get_global_symbol { ast2ct } s =
    try
      Some (fst @@ D.Symbol.RawMap.find s ast2ct)
    with Not_found ->
      None

  let empty () =
    if not @@ D.Global_symbols.table.locked then
      anomaly "SymbolMap created before Global_symbols.table is locked";

    let table = {
      ast2ct = D.Global_symbols.( table.s2ct);
      last_global = D.Global_symbols.table.last_global;
      c2s = D.Global_symbols.table.c2s;
      c2t = Util.Constants.Map.map (fun s ->
        let _, t = D.Symbol.RawMap.find s D.Global_symbols.(table.s2ct) in
        t) D.Global_symbols.(table.c2s);
    } in
    (*T2.go allocate_global_symbol_aux*) 
    table
    
  let allocate_global_symbol state table (x:D.Symbol.t) =
    if not (D.State.get D.while_compiling state) then
      anomaly (Format.asprintf "Cannot allocate a symbol for %a. Global symbols can only be allocated during compilation" D.Symbol.pp x);
    allocate_global_symbol_aux x table

  let allocate_bound_symbol_aux n ({ c2t; ast2ct } as table) =
    try table, Util.Constants.Map.find n c2t
    with Not_found ->
      let xx = D.Term.Const n in
      let c2t = Util.Constants.Map.add n xx c2t in
      { table with c2t; ast2ct }, xx

  let allocate_bound_symbol state table n =
    if n < 0 then
      anomaly "bound variables are positive";
    allocate_bound_symbol_aux n table
  ;;

  let get_canonical state table c =
    if not (D.State.get D.while_compiling state) then
      D.Const c
    else
      try Util.Constants.Map.find c table.c2t
      with Not_found -> anomaly ("unknown symbol " ^ string_of_int c)

  let global_name state table c =
    if not (D.State.get D.while_compiling state) then
      anomaly "get_canonical can only be used during compilation";
    try Symbol.get_func @@ Util.Constants.Map.find c table.c2s
    with Not_found -> anomaly ("unknown symbol " ^ string_of_int c)

end

module Builtins : sig

  type t
  val pp : Format.formatter -> t -> unit
  val register : t -> D.BuiltInPredicate.t -> constant -> t
  val is_declared : t -> constant -> bool
  val fold : (constant -> Data.BuiltInPredicate.t -> 'a -> 'a) -> t -> 'a -> 'a
  val empty : t

end = struct
  type t = Data.BuiltInPredicate.t Constants.Map.t
  [@@deriving show]
  let empty = Constants.Map.empty
  let fold = Constants.Map.fold

let register t (D.BuiltInPredicate.Pred(s,_,_) as b) idx =
  if s = "" then anomaly "Built-in predicate name must be non empty";
  if Constants.Map.mem idx t then
    anomaly ("Duplicate built-in predicate " ^ s);
  Constants.Map.add idx b t
;;

let is_declared t x = Constants.Map.mem x t

end

(****************************************************************************
  Intermediate program representation
 ****************************************************************************)

open Data
module C = Constants

open Compiler_data

module UF = Symbol.UF

type macro_declaration = (ScopedTerm.t * Loc.t) F.Map.t
[@@ deriving show, ord]

module Scoped = struct


type program = {
  pbody : pbody;
  toplevel_macros : macro_declaration;
}
and pbody = {
  kinds : Arity.t F.Map.t;
  types : ScopeTypeExpressionUniqueList.t F.Map.t;
  type_abbrevs : (F.t * ScopedTypeExpression.t) list;
  body : block list;
  pred_symbols : F.Set.t;
  ty_symbols : F.Set.t;
}
and block =
  | Clauses of (ScopedTerm.t,Ast.Structured.attribute,bool,bool) Ast.Clause.t list (* TODO: use a map : predicate -> clause list to speed up insertion *)
  | Namespace of string * pbody
  | Shorten of F.t Ast.Structured.shorthand list * pbody
  | Constraints of (F.t,ScopedTerm.t) Ast.Structured.block_constraint * pbody
  | Accumulated of pbody
[@@deriving show]

end



module Flat = struct

type unchecked_signature = {
  toplevel_macros : macro_declaration;
  kinds : Arity.t F.Map.t;
  types : ScopeTypeExpressionUniqueList.t F.Map.t;
  type_abbrevs : (F.t * ScopedTypeExpression.t) list;
}
[@@deriving show]

type program = {
  signature : unchecked_signature;
  clauses : (ScopedTerm.t,Ast.Structured.attribute,bool,bool) Ast.Clause.t list;
  chr : (F.t,ScopedTerm.t) Ast.Structured.block_constraint list;
  builtins : BuiltInPredicate.t list;
}
[@@deriving show]

end


module Assembled = struct

  type signature = {
    toplevel_macros : macro_declaration;
    kinds : Arity.t F.Map.t;
    types : Type_checker.typing_env;
    type_abbrevs : Type_checker.type_abbrevs;
  }
  [@@deriving show]
  
  
  type program = {
    (* for printing only *)
    clauses : (Ast.Structured.insertion option * string option * constant * clause) list;
  
    signature : signature;

    total_type_checking_time : float;
  
    builtins : Builtins.t;
    prolog_program : index;
    indexing : (Mode.hos * indexing) C.Map.t;
    chr : CHR.t;
  
    symbols : SymbolMap.table;
  
    hash : string;
  
  }
  [@@deriving show]
  
  let empty_signature () = {
    kinds = F.Map.empty;
    types = Type_checker.empty_typing_env;
    type_abbrevs = F.Map.empty;
    toplevel_macros = F.Map.empty;
  }
  let empty () = {
    clauses = [];
    prolog_program = { idx = Ptmap.empty; time = 0; times = StrMap.empty };
    indexing = C.Map.empty;
    chr = CHR.empty;
    symbols = SymbolMap.empty ();
    total_type_checking_time = 0.0;
    hash = "";
    builtins = Builtins.empty;
    signature = empty_signature ()
  }
  
  end


module CheckedFlat = struct

type program = {
  signature : Assembled.signature;
  clauses : (ScopedTerm.t,Ast.Structured.attribute,bool,bool) Ast.Clause.t list;
  chr : (Symbol.t,ScopedTerm.t) Ast.Structured.block_constraint list;
  builtins : (Symbol.t * BuiltInPredicate.t) list;
}
[@@deriving show]

end

type scoped_program = {
  version : string;
  code : Scoped.program;
}
[@@deriving show]

type unchecked_compilation_unit = {
  version : string;
  code : Flat.program;
}
[@@deriving show]

(* TODO: proper hash *)
let hash_base x = string_of_int @@ Hashtbl.hash x 


type checked_compilation_unit = {
  version : string;
  checked_code : CheckedFlat.program;
  base_hash : string;
  precomputed_signature : Assembled.signature;
  type_checking_time : float;
}
[@@deriving show]

type checked_compilation_unit_signature = Assembled.signature
[@@deriving show]


let signature_of_checked_compilation_unit { checked_code = { CheckedFlat.signature } } = signature




type builtins = string * Data.BuiltInPredicate.declaration list

type program = State.t * Assembled.program
type header = program


module WithMain = struct

(* The entire program + query, but still in "printable" format *)
type query = {  
  prolog_program : index;
  chr : CHR.t;
  symbols : SymbolMap.table;
  initial_goal : term;
  assignments : term StrMap.t;
  compiler_state : State.t;
  total_type_checking_time : float;
  builtins : Builtins.t;

}
[@@deriving show]

end
type query = WithMain.query

(****************************************************************************
  Compiler
 ****************************************************************************)

let valid_functional = function [] -> Some Ast.Structured.Relation | [Ast.Functional] -> Some Function | _ -> None

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
      | (External _ | Index _ | Functional) as a :: _-> illegal_err a
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
      | (Before _ | After _ | Replace _ | Remove _ | External _ | Index _ | Functional | Untyped) as a :: _ -> illegal_err a 
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


  (* 
    replaces 
    - TArr (t1,t2) when t2 = Prop    -> TPred (o:t1),
    - TArr (t1,t2) when t2 = TPred l -> TPred (o:t1, l)
  *)
  let flatten_arrows toplevel_func =
    let is_propf f = F.equal F.propf f || F.equal F.fpropf f in
    let rec is_pred = function 
      | Ast.TypeExpression.TConst a -> is_propf a
      | TArr(_,r) -> is_pred r.tit
      | TApp (_, _, _) | TPred (_, _) -> false
    in
    let rec flatten tloc = function
      | Ast.TypeExpression.TArr (l,r) -> (Ast.Mode.Output, l) :: flatten_loc r 
      | TConst c when is_propf c -> [] 
      | tit -> [Output,{tit;tloc}]
    and flatten_loc {tit;tloc} = flatten tloc tit
    and main = function
      | Ast.TypeExpression.TPred (b, l) -> 
          Ast.TypeExpression.TPred (b, List.map (fun (a, b) -> a, main_loc b) l)
      | TConst _ as t -> t
      | TApp (n, x, xs) -> TApp (n, main_loc x, List.map main_loc xs)
      | TArr (l, r) when is_pred r.tit -> TPred (toplevel_func, (Output, main_loc l) :: flatten_loc r)
      | TArr (l, r) -> TArr(main_loc l, main_loc r)
    and main_loc {tit;tloc} = {tit=main tit;tloc}
    in main_loc

  let structure_type_expression loc toplevel_func valid t = 
    let res = match t.TypeExpression.tit with
      | TPred([],p) ->
        { t with tit = TPred(toplevel_func,List.map (fun (m,p) -> m, structure_type_expression_aux ~loc valid p) p) }
      | x -> structure_type_expression_aux ~loc valid t
      in flatten_arrows toplevel_func res

  let structure_kind_attributes { Type.attributes; loc; name; ty } =
    let ty = structure_type_expression loc () (function [] -> Some () | _ -> None) ty in
    match attributes with
    | [] -> { Type.attributes = (); loc; name; ty }
    | x :: _ -> error ~loc ("illegal attribute " ^ show_raw_attribute x)

  let structure_external ~loc = function
    | None -> None
    | Some "core" -> Some Core
    | Some s ->
        try Some (Builtin { variant = int_of_string s })
        with Invalid_argument _ -> error ~loc ("illegal external attribute")


  let structure_type_attributes { Type.attributes; loc; name; ty } =
    let duplicate_err s =
      error ~loc ("duplicate attribute " ^ s) in
    let illegal_err a =
      error ~loc ("illegal attribute " ^ show_raw_attribute a) in
    let rec aux_tatt r f = function
      | [] -> r, f
      | External o :: rest ->
         begin match r with
           | None -> aux_tatt (Some (Structured.External (structure_external ~loc o))) f rest
           | Some (Structured.External _) -> duplicate_err "external"
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
    (* if F.equal name (F.from_string "std.map") then
    Format.eprintf "Type for %a is %a@." F.pp name (TypeExpression.pp (pplist pp_raw_attribute " ")) ty; *)
    let is_functional_from_ty () = match ty.tit with
      | TPred (l, _) -> List.mem Functional l | _ -> false in
    let attributes =
      match attributes with
      | None -> 
        if toplevel_func = Function || is_functional_from_ty () then Some MaximizeForFunctional
        else None
      | Some _ as x -> x in
    let ty = structure_type_expression loc toplevel_func valid_functional ty in
    { Type.attributes; loc; name; ty }

  let structure_type_abbreviation { TypeAbbreviation.name; value; nparams; loc } =
    let rec aux = function
      | TypeAbbreviation.Lam(c,loc,t) -> TypeAbbreviation.Lam(c,loc,aux t)
      | TypeAbbreviation.Ty t -> TypeAbbreviation.Ty (structure_type_expression loc Relation valid_functional t)
  in
  { TypeAbbreviation.name; value = aux value; nparams; loc }

  let run _ dl =
    let rec aux_run ns blocks clauses macros kinds types tabbrs chr accs = function
      | Program.Ignored _ :: rest ->
          aux_run ns blocks clauses macros kinds types tabbrs chr accs rest
      | (Program.End _ :: _ | []) as rest ->
          { body = List.rev (cl2b clauses @ blocks);
            types = (*List.rev*) types; (* we prefer the last one *)
            kinds = List.rev kinds;
            type_abbrevs = List.rev tabbrs;
            macros = List.rev macros },
          List.rev chr,
          rest
      | Program.Begin loc :: rest ->
          let p, chr1, rest = aux_run ns [] [] [] [] [] [] [] accs rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside an anonymous block";
          aux_end_block loc ns (Accumulated p :: cl2b clauses @ blocks)
            [] macros kinds types tabbrs chr accs rest
      | Program.Constraint (loc, ctx_filter, clique) :: rest ->
          if chr <> [] then
            error "Constraint blocks cannot be nested";
          let p, chr, rest = aux_run ns [] [] [] [] [] [] [] accs rest in
          aux_end_block loc ns (Constraints({loc;ctx_filter;clique;rules=chr},p) :: cl2b clauses @ blocks)
            [] macros kinds types tabbrs [] accs rest
      | Program.Namespace (loc, n) :: rest ->
          let p, chr1, rest = aux_run (n::ns) [] [] [] [] [] [] [] StrSet.empty rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside a namespace block";
          aux_end_block loc ns (Namespace (n,p) :: cl2b clauses @ blocks)
            [] macros kinds types tabbrs chr accs rest
      | Program.Shorten (loc,[]) :: _ ->
          anomaly ~loc "parser returns empty list of shorten directives"
      | Program.Shorten (loc,directives) :: rest ->
          let shorthand (full_name,short_name) = { iloc = loc; full_name; short_name } in
          let shorthands = List.map shorthand directives in
          let p, chr1, rest = aux_run ns [] [] [] [] [] [] [] accs rest in
          if chr1 <> [] then
            error "CHR cannot be declared after a shorthand";
          aux_run ns ((Shorten(shorthands,p) :: cl2b clauses @ blocks))
            [] macros kinds types tabbrs chr accs rest

      | Program.Accumulated (_,[]) :: rest ->
          aux_run ns blocks clauses macros kinds types tabbrs chr accs rest

      | Program.Accumulated (loc,{ file_name; digest; ast = a } :: more) :: rest ->
          let rest = Program.Accumulated (loc, more) :: rest in
          let digest = String.concat "." (digest :: List.map F.show ns) in
          if StrSet.mem digest accs then begin
            (* Printf.eprintf "skip: %s\n%!" filename; *)
            aux_run ns blocks clauses macros kinds types tabbrs chr accs rest
          end else begin
            (* Printf.eprintf "acc: %s -> %d\n%!" filename (List.length a); *)
            aux_run ns blocks clauses macros kinds types tabbrs chr
              (StrSet.add digest accs)
              (Program.Begin loc :: a @ Program.End loc :: rest)
          end

      | Program.Clause c :: rest ->
          let c = structure_clause_attributes c in
          aux_run ns blocks (c::clauses) macros kinds types tabbrs chr accs rest
      | Program.Macro m :: rest ->
          aux_run ns blocks clauses (m::macros) kinds types tabbrs chr accs rest
      | Program.Pred t :: rest ->
          let t = structure_type_attributes t in
          aux_run ns blocks clauses macros kinds (t :: types) tabbrs chr accs rest
      | Program.Kind [] :: rest ->
          aux_run ns blocks clauses macros kinds types tabbrs chr accs rest
      | Program.Kind (k::ks) :: rest ->          
          let k = structure_kind_attributes k in
          aux_run ns blocks clauses macros (k :: kinds) types tabbrs chr accs (Program.Kind ks :: rest)
      | Program.Type [] :: rest ->
          aux_run ns blocks clauses macros kinds types tabbrs chr accs rest
      | Program.Type (t::ts) :: rest ->          
          if List.mem Functional t.attributes then error ~loc:t.loc "functional attribute only applies to pred";
          let t = structure_type_attributes t in
          aux_run ns blocks clauses macros kinds (t :: types) tabbrs chr accs (Program.Type ts :: rest)
      | Program.TypeAbbreviation abbr :: rest ->
          let abbr = structure_type_abbreviation abbr in
          aux_run ns blocks clauses macros kinds types (abbr :: tabbrs) chr accs rest
      | Program.Chr r :: rest ->
          let r = structure_chr_attributes r in
          aux_run ns blocks clauses macros kinds types tabbrs (r::chr) accs rest

    and aux_end_block loc ns blocks clauses macros kinds types tabbrs chr accs rest =
      match rest with
      | Program.End _ :: rest ->
          aux_run ns blocks clauses macros kinds types tabbrs chr accs rest
      | _ -> error ~loc "matching } is missing"

    in
    let blocks, chr, rest = aux_run [] [] [] [] [] [] [] [] StrSet.empty dl in
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
    ~compilation_is_over:(fun x -> Some x)
    ~execution_is_over:(fun x -> Some x)
    ~init:(fun () -> StrMap.empty)
    ()
  let default_quotation : QuotationHooks.quotation option State.component = State.declare
    ~descriptor:elpi_state_descriptor
    ~name:"elpi:default_quotation"
    ~pp:(fun _ _ -> ())
    ~clause_compilation_is_over:(fun b -> b)
    ~compilation_is_over:(fun x -> Some x)
    ~execution_is_over:(fun x -> Some x)
    ~init:(fun () -> None)
    ()

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
  ~compilation_is_over:(fun x -> Some x)
  ~execution_is_over:(fun x -> Some x)
  ~init:(fun () -> None)
  ()

  let backtick  : (string * QuotationHooks.quotation) option State.component = State.declare
  ~descriptor:elpi_state_descriptor
  ~name:"elpi:backtick"
  ~pp:(fun _ _ -> ())
  ~clause_compilation_is_over:(fun b -> b)
  ~compilation_is_over:(fun x -> Some x)
  ~execution_is_over:(fun x -> Some x)
  ~init:(fun () -> None)
  ()

  let scope_singlequote ~loc state x = 
    match State.get singlequote state with
    | None -> ScopedTerm.(Const(ScopedTerm.mk_global x))
    | Some (language,f) -> ScopedTerm.unlock @@ ScopedTerm.of_simple_term_loc @@ f ~language state loc (F.show x)
  let scope_backtick ~loc state x =
    match State.get backtick state with
    | None -> ScopedTerm.(Const(ScopedTerm.mk_global x))
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
  needs_spilling : bool ref;
}
let empty_mtm = { macros = F.Map.empty; ctx = F.Set.empty; needs_spilling = ref false }
let todopp name _fmt _ = error ("pp not implemented for field: "^name)

let get_mtm, set_mtm, _drop_mtm, update_mtm =
  let mtm =
    State.declare
     ~name:"elpi:mtm" ~pp:(todopp "elpi:mtm")
     ~descriptor:D.elpi_state_descriptor
     ~clause_compilation_is_over:(fun _ -> empty_mtm)
      ~compilation_is_over:(fun _ -> None)
      ~execution_is_over:(fun _ -> None)
      ~init:(fun () -> empty_mtm) 
    () in
  State.(get mtm, set mtm, drop mtm, update mtm)

module Scope_Quotation_Macro : sig

  val run : State.t -> toplevel_macros:macro_declaration -> Ast.Structured.program -> Scoped.program
  val scope_loc_term : state:State.t -> Ast.Term.t -> ScopedTerm.t

end = struct
  let map_append Ast.Type.{name;loc} v m =
    let k = name in
    try
      let l = F.Map.find k m in
      F.Map.add k (ScopeTypeExpressionUniqueList.merge v l) m
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

  let rec pred2arr ctx ~loc func = function
    | [] -> ScopedTypeExpression.Prop func
    | (m,x)::xs -> Arrow (m,NotVariadic,scope_loc_tye ctx x, {loc; it=pred2arr ctx ~loc func xs})

  and scope_tye ctx ~loc t : ScopedTypeExpression.t_ =
    match t with
    | Ast.TypeExpression.TConst c when F.equal F.propf c -> Prop Relation
    | Ast.TypeExpression.TConst c when F.equal F.fpropf c -> Prop Function
    | TConst c when F.show c = "any" -> Any
    | TConst c when F.Set.mem c ctx -> Const(Bound elpi_language,c)
    | TConst c when is_global c -> Const(Scope.mkGlobal ~escape_ns:true (),of_global c)
    | TConst c -> Const(Scope.mkGlobal(),c)
    | TApp(c,x,[y]) when F.show c = "variadic" ->
        (* Convention all arguments of a variadic function are in input *)
        Arrow(Input, Variadic,scope_loc_tye ctx x,scope_loc_tye ctx y)
    | TApp(c,x,xs) when is_global c ->
        App(Scope.mkGlobal ~escape_ns:true (), of_global c, scope_loc_tye ctx x, List.map (scope_loc_tye ctx) xs)
    | TApp(c,x,xs) ->
        if F.Set.mem c ctx || is_uvar_name c then error ~loc "type schema parameters cannot be type formers";
        App(Scope.mkGlobal (),c,scope_loc_tye ctx x, List.map (scope_loc_tye ctx) xs)
    | TPred(m,xs) -> pred2arr ctx ~loc m xs
    | TArr(s,t) -> Arrow(Output, NotVariadic, scope_loc_tye ctx s, scope_loc_tye ctx t)
  and scope_loc_tye ctx { tloc; tit } = { loc = tloc; it = scope_tye ctx ~loc:tloc tit }
  let scope_loc_tye ctx (t: Ast.Structured.functionality Ast.TypeExpression.t) =
    scope_loc_tye ctx t

  let compile_type { Ast.Type.name; loc; attributes; ty } =
    let open ScopedTypeExpression in
    let value = scope_loc_tye F.Set.empty ty in
    let vars =
      let rec aux e { it } =
        match it with
        | App(_,_,x,xs) -> List.fold_left aux e (x :: xs)
        | Const(Bound _, _) -> assert false (* there are no binders yet *)
        | Const(Global _,c) when is_uvar_name c -> F.Set.add c e
        | Const(Global _,_) -> e
        | Any | Prop _ -> e
        | Arrow(_,_,x,y) -> aux (aux e x) y
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
    { ScopedTypeExpression.name; indexing = attributes; loc; nparams; value }

  let scope_term_macro ~loc ~state c args =
    let { macros } = get_mtm state in
    match F.Map.find_opt c macros with
    | None -> error ~loc (Format.asprintf "@[<hv>Unknown macro %a.@ Known macros: %a@]" F.pp c (pplist F.pp ", ") (F.Map.bindings macros|>List.map fst))
    | Some (t, _) -> ScopedTerm.beta (ScopedTerm.clone_loc t) args

  let rec scope_term ~state ctx ~loc t =
    let open Ast.Term in
    match t with
    | Parens { loc; it } -> scope_term ~state ctx ~loc it
    | Const c when is_discard c -> ScopedTerm.Discard
    | Const c when is_macro_name c ->
        scope_term_macro ~loc ~state c []
    | Const c when F.Set.mem c ctx -> ScopedTerm.(Const(ScopedTerm.mk_ty_bound_elpi elpi_language c))
    | Const c ->
        if is_uvar_name c then ScopedTerm.Var(ScopedTerm.mk_ty_bound_elpi elpi_var c,[])
        else if CustomFunctorCompilation.is_singlequote c then CustomFunctorCompilation.scope_singlequote ~loc state c
        else if CustomFunctorCompilation.is_backtick c then CustomFunctorCompilation.scope_backtick ~loc state c
        else if is_global c then ScopedTerm.(Const(mk_ty_name (Scope.mkGlobal ~escape_ns:true ()) (of_global c)))
        else ScopedTerm.(Const(mk_ty_name (Scope.mkGlobal ()) c))
    | App ({ it = App (f,l1) },l2) -> scope_term ~state ctx ~loc (App(f, l1 @ l2))
    | App ({ it = Parens f },l) -> scope_term ~state ctx ~loc (App(f, l))
    | App({ it = Const c }, [x]) when F.equal c F.spillf ->
        let { needs_spilling } = get_mtm state in
        needs_spilling := true;
        ScopedTerm.Spill (scope_loc_term ~state ctx x,ref ScopedTerm.NoInfo)
    | App({ it = Const c }, l) when F.equal c F.implf || F.equal c F.rimplf ->
        begin match l with 
        | [t1;t2] ->           
          (* Printf.eprintf "LHS= %s\n" (Ast.Term.show t1); *)
          Impl (F.equal c F.implf, scope_loc_term ~state ctx t1, scope_loc_term ~state ctx t2)
        | _ -> error ~loc "implication is a binary operator"
        end
    | App({ it = Const c }, x :: xs) ->
         if is_discard c then error ~loc "Applied discard";
         let x = scope_loc_term ~state ctx x in
         let xs = List.map (scope_loc_term ~state ctx) xs in
         if is_macro_name c then
           scope_term_macro ~loc ~state c (x::xs)
         else
          let bound = F.Set.mem c ctx in
          if bound then ScopedTerm.App(ScopedTerm.mk_ty_bound_elpi elpi_language c, x, xs)
          else if is_uvar_name c then ScopedTerm.Var(ScopedTerm.mk_ty_bound_elpi elpi_var c,x :: xs)
          else if is_global c then ScopedTerm.App(ScopedTerm.mk_ty_name (Scope.mkGlobal ~escape_ns:true ()) (of_global c),x,xs)
          else ScopedTerm.App(ScopedTerm.mk_ty_name (Scope.mkGlobal ()) c, x, xs)
    | Cast (t,ty) ->
        let t = scope_loc_term ~state ctx t in
        let ty = scope_loc_tye F.Set.empty (RecoverStructure.structure_type_expression ty.Ast.TypeExpression.tloc Ast.Structured.Relation valid_functional ty) in
        ScopedTerm.Cast(t,ty)
    | Lam (c,ty,b) when is_discard c ->
        let ty = ty |> Option.map (fun ty -> scope_loc_tye F.Set.empty (RecoverStructure.structure_type_expression ty.Ast.TypeExpression.tloc Ast.Structured.Relation valid_functional ty)) in
        ScopedTerm.Lam (None,ty, scope_loc_term ~state ctx b)
    | Lam (c,ty,b) ->
        if has_dot c then error ~loc "Bound variables cannot contain the namespaec separator '.'";
        let ty = ty |> Option.map (fun ty -> scope_loc_tye F.Set.empty (RecoverStructure.structure_type_expression ty.Ast.TypeExpression.tloc Ast.Structured.Relation valid_functional ty)) in
        let name = Some (ScopedTerm.mk_ty_name elpi_language c) in
        ScopedTerm.Lam (name,ty,scope_loc_term ~state (F.Set.add c ctx) b)
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
      { ScopedTerm.it; loc; ty = TypeAssignment.new_ty () }

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

  let defs_of_map m = F.Map.bindings m |> List.fold_left (fun x (a,_) -> F.Set.add a x) F.Set.empty
  let defs_of_assoclist m = m |> List.fold_left (fun x (a,_) -> F.Set.add a x) F.Set.empty

  let global_hd_symbols_of_clauses cl =
    let open ScopedTerm in
    let add1 s t =
      match t.it with
      | Const(Global _,c,_) | App((Global _,c,_),_,_) -> F.Set.add c s
      | Impl(false,{ it = (Const(Global _,c,_) | App((Global _,c,_),_,_)) }, _) -> F.Set.add c s
      | _ -> assert false in
    List.fold_left (fun s { Ast.Clause.body } ->
      match body.it with
      | App((Global _,c,_),x,xs) when F.equal F.andf c ->
        (* since we allow a rule to be of the form (p :- ..., q :- ...) eg
           via macro expansion, we could have , in head position  *)
          List.fold_left add1 s (x::xs)
      | _ -> add1 s body)
      F.Set.empty cl

  let compile_clause state macros { Ast.Clause.body; attributes; loc; needs_spilling = () } =
     let needs_spilling = ref false in
     let state = set_mtm state { empty_mtm with macros; needs_spilling } in
     let body = scope_loc_term ~state body in
     { Ast.Clause.body; attributes; loc; needs_spilling = !needs_spilling; is_deterministic = false }


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
      | TArr({ tit = TConst c },t) when F.equal c F.typef -> 1 + count t.tit
      | TConst c when F.equal c F.typef -> 0
      | x -> error ~loc "Syntax error: illformed kind.\nExamples:\nkind bool type.\nkind list type -> type.\n"
    in
    F.Map.add name (count ty.tit, loc) kinds  
    
  let compile_macro state (am,m) { Ast.Macro.loc; name; body } =
    try
      let _, oloc = F.Map.find name m in
      error ~loc (Format.asprintf "duplicate macro %a, previous declaration %a" F.pp name Loc.pp oloc)
    with Not_found ->
      let body = scope_loc_term ~state:(set_mtm state { empty_mtm with macros = m }) body in
      F.Map.add name (body,loc) am, F.Map.add name (body,loc) m

  let run state ~toplevel_macros p : Scoped.program =

    let rec compile_program omacros state { Ast.Structured.macros; kinds; types; type_abbrevs; body } =
      let toplevel_macros, active_macros = List.fold_left (compile_macro state) (F.Map.empty,omacros) macros in
      let type_abbrevs = List.map compile_type_abbrev type_abbrevs in
      let kinds = List.fold_left compile_kind F.Map.empty kinds in
      let types = List.fold_left (fun m t -> map_append t (ScopeTypeExpressionUniqueList.make @@ compile_type t) m) F.Map.empty (List.rev types) in
      let defs_k = defs_of_map kinds in
      let defs_t = defs_of_map types in
      let defs_ta = defs_of_assoclist type_abbrevs in
      let kinds, types, type_abbrevs, defs_b, defs_ty, body =
        compile_body active_macros kinds types type_abbrevs F.Set.empty F.Set.empty state body in
      let ty_symbols = F.Set.(union defs_k (union defs_t (union defs_ta defs_ty))) in
      let pred_symbols = F.Set.(union defs_t defs_b) in
      (* Format.eprintf "CP: types: %d\n" (F.Map.cardinal types);
      Format.eprintf "CP: ty_sym: %a\n" F.Set.pp ty_symbols; *)
      toplevel_macros,
      { Scoped.types; kinds; type_abbrevs; body; ty_symbols; pred_symbols }

    and compile_body macros kinds types type_abbrevs (defs : F.Set.t) (ty_defs : F.Set.t) state = function
      | [] -> kinds, types, type_abbrevs, defs, ty_defs, []
      | Clauses cl :: rest ->
          let compiled_cl = List.map (compile_clause state macros) cl in
          let defs = F.Set.union defs (global_hd_symbols_of_clauses compiled_cl) in
          let kinds, types, type_abbrevs, defs, ty_defs, compiled_rest =
            compile_body macros kinds types type_abbrevs defs ty_defs state rest in
          let compiled_rest =
            match compiled_rest with
            | Scoped.Clauses l :: rest -> Scoped.Clauses (compiled_cl @ l) :: rest
            | rest -> Scoped.Clauses compiled_cl :: rest in
          kinds, types, type_abbrevs, defs, ty_defs, compiled_rest
      | Namespace (prefix, p) :: rest ->
          let prefix = F.show prefix in
          let _, p = compile_program macros state p in
          let kinds, types, type_abbrevs, defs, ty_defs, compiled_rest =
            compile_body macros kinds types type_abbrevs defs ty_defs state rest in
          let ty_symbols = prepend [prefix] p.Scoped.ty_symbols in
      (* Format.eprintf "CB: ty_sym %s: %a\n" prefix F.Set.pp ty_symbols; *)
          let pred_symbols = prepend [prefix] p.Scoped.pred_symbols in
          kinds, types, type_abbrevs, F.Set.union defs pred_symbols, F.Set.union ty_defs ty_symbols,
          Scoped.Namespace(prefix, p) :: compiled_rest
      | Shorten(shorthands,p) :: rest ->
          let shorts = List.fold_left (fun s { Ast.Structured.short_name } ->
            F.Set.add short_name s) F.Set.empty shorthands in
          let _, p = compile_program macros state p in
          let kinds, types, type_abbrevs, defs, ty_defs, compiled_rest =
            compile_body macros kinds types type_abbrevs defs ty_defs state rest in
          kinds, types, type_abbrevs,
          F.Set.union defs (F.Set.diff p.Scoped.pred_symbols shorts), (* TODO shorten/ shorten-ty *)
          F.Set.union ty_defs (F.Set.diff p.Scoped.ty_symbols shorts),
          Scoped.Shorten(shorthands, p) :: compiled_rest
      | Constraints ({loc;ctx_filter; clique; rules}, p) :: rest ->
          (* XXX missing check for nested constraints *)
          let rules = List.map (compile_chr_rule state macros) rules in
          let _, p = compile_program macros state p in
          let kinds, types, type_abbrevs, defs, ty_defs, compiled_rest =
            compile_body macros kinds types type_abbrevs defs ty_defs state rest in
          kinds, types, type_abbrevs,
          F.Set.union defs p.Scoped.pred_symbols,
          F.Set.union ty_defs p.Scoped.ty_symbols,
          Scoped.Constraints({loc;ctx_filter; clique; rules},p) :: compiled_rest
      | Accumulated p :: rest ->
          let _, p = compile_program macros state p in
          let kinds, types, type_abbrevs, defs, ty_defs, compiled_rest =
            compile_body macros kinds types type_abbrevs defs ty_defs state rest in
          kinds, types, type_abbrevs,
          F.Set.union defs p.Scoped.pred_symbols,
          F.Set.union ty_defs p.Scoped.ty_symbols,
          Scoped.Accumulated p :: compiled_rest
  
    in
    let toplevel_macros, pbody = compile_program toplevel_macros state p in
    (* Printf.eprintf "run: %d\n%!" (F.Map.cardinal toplevel_macros); *)
    { Scoped.pbody; toplevel_macros }

end

module Flatten : sig

  (* Eliminating the structure (name spaces) *)

  val run : State.t -> Scoped.program -> Flat.program
  val merge_kinds :
    Arity.t F.Map.t ->
    Arity.t F.Map.t ->
    Arity.t F.Map.t
  val merge_type_assignments :
    Type_checker.typing_env ->
    Type_checker.typing_env ->
      Type_checker.typing_env
  val merge_checked_type_abbrevs :
    Type_checker.type_abbrevs ->
    Type_checker.type_abbrevs ->
    Type_checker.type_abbrevs
  val merge_toplevel_macros :
    (ScopedTerm.t * Loc.t) F.Map.t ->
    (ScopedTerm.t * Loc.t) F.Map.t -> (ScopedTerm.t * Loc.t) F.Map.t

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


  let smart_map_scoped_term f ~tyf:tyf t =
    let open ScopedTerm in
    let rec aux it =
      match it with
      | Impl(b,t1,t2) -> 
          let t1' = aux_loc t1 in
          let t2' = aux_loc t2 in
          if t1 == t1' && t2 == t2' then it
          else Impl(b,t1',t2')
      | Const((Bound _|Global { escape_ns = true }),_,_) -> it
      | Const(Global { escape_ns = false },c,ty) -> let c' = f c in if c == c' then it else Const(Scope.mkGlobal (),c',ty)
      | Spill(t,n) -> let t' = aux_loc t in if t' == t then it else Spill(t',n)
      | App((scope,c,ty),x,xs) ->
          let c' = if scope = Scope.mkGlobal () then f c else c in
          let x' = aux_loc x in
          let xs' = smart_map aux_loc xs in
          if c == c' && x == x' && xs == xs' then it
          else App((scope,c',ty),x',xs')
      | Lam(n,ty,b) ->
          let b' = aux_loc b in
          let ty' = option_smart_map (ScopedTypeExpression.smart_map_scoped_loc_ty tyf) ty in
          if b == b' && ty' == ty then it else Lam(n,ty',b')
      | Var(c,l) ->
          let l' = smart_map aux_loc l in
          if l == l' then it else Var(c,l')
      | Cast(t,ty) ->
          let t' = aux_loc t in
          let ty' = ScopedTypeExpression.smart_map_scoped_loc_ty tyf ty in
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

  let apply_subst_clauses s ty_s cl =
    smart_map (smart_map_clause (smart_map_scoped_term (subst_global s) ~tyf:(subst_global ty_s))) cl

  let smart_map_sequent f ~tyf ({ Ast.Chr. eigen; context; conclusion } as orig) =
    let eigen' = smart_map_scoped_term f ~tyf eigen in
    let context' = smart_map_scoped_term f ~tyf context in
    let conclusion' = smart_map_scoped_term f ~tyf conclusion in
    if eigen' == eigen && context' == context && conclusion' == conclusion then orig
    else { Ast.Chr.eigen = eigen'; context = context'; conclusion = conclusion' }

  let smart_map_chr f ~tyf ({ Ast.Chr.to_match; to_remove; guard; new_goal; attributes; loc } as orig) =
    let to_match' = smart_map (smart_map_sequent f ~tyf) to_match in
    let to_remove' = smart_map (smart_map_sequent f ~tyf) to_remove in
    let guard' = Util.option_map (smart_map_scoped_term f ~tyf) guard in
    let new_goal' = Util.option_map (smart_map_sequent f ~tyf) new_goal in
    if to_match' == to_match && to_remove' == to_remove && guard' == guard && new_goal' == new_goal then orig
    else { Ast.Chr.to_match = to_match'; to_remove = to_remove'; guard = guard'; new_goal = new_goal'; attributes; loc }

  let smart_map_chrs f ~tyf ({ Ast.Structured.clique; ctx_filter; rules; loc } as orig) =
    let clique' = smart_map f clique in
    let ctx_filter' = smart_map f ctx_filter in
    let rules' = smart_map (smart_map_chr f ~tyf) rules in
    if clique' == clique && ctx_filter' == ctx_filter && rules' == rules then orig
    else { Ast.Structured.clique = clique'; ctx_filter = ctx_filter'; rules = rules'; loc }

  let apply_subst_chrs s sty = smart_map_chrs (subst_global s) ~tyf:(subst_global sty)


  let apply_subst_types s = ScopeTypeExpressionUniqueList.smart_map (ScopedTypeExpression.smart_map (subst_global s))

  let apply_subst_types s l =
    F.Map.fold (fun k v m -> F.Map.add (subst_global s k) (apply_subst_types s v) m) l F.Map.empty

  let apply_subst_kinds s l =
    F.Map.fold (fun k v m -> F.Map.add (subst_global s k) v m) l F.Map.empty
  
  let apply_subst_type_abbrevs s l =
    List.map (fun (k, v) -> subst_global s k, ScopedTypeExpression.smart_map (subst_global s) v) l

  let merge_indexing s idx1 idx2 =
    if not @@ Type_checker.compatible_indexing idx1 idx2 then
      error ~loc:(Symbol.get_loc s) ("Incompatible indexing options for symbol " ^ Symbol.get_str s);
    idx1

  let merge_symbol_metadata s { Type_checker.ty = ty1; indexing = idx1 } { Type_checker.ty = ty2; indexing = idx2 } =
    { Type_checker.ty = TypeAssignment.merge_skema ty1 ty2;
      indexing = merge_indexing s idx1 idx2;
    }

  let merge_type_assignments { Type_checker.symbols = s1; overloading = o1 } { Type_checker.symbols = s2; overloading = o2 } =
    let symbols = Symbol.QMap.union merge_symbol_metadata s1 s2 in
    let to_unite = ref [] in
    let overloading = F.Map.union (fun f l1 l2 ->
      (* We give precedence to recent type declarations over old ones *)
      let to_u, l = TypeAssignment.undup_skemas (fun x -> (Symbol.QMap.find x symbols).ty) l1 l2 in
      to_unite := to_u :: !to_unite;
      Some l
      ) o1 o2 in
    let to_unite = List.concat !to_unite in
    let symbols =
      List.fold_right (fun (x,y) -> Symbol.QMap.unify merge_symbol_metadata x y) to_unite symbols in
    { Type_checker.overloading; symbols }

  let merge_checked_type_abbrevs m1 m2 =
    let m = F.Map.union (fun k (sk,otherloc as x) (ty,loc) ->
      if TypeAssignment.compare_skema sk ty <> 0 then
        error ~loc
        ("Duplicate type abbreviation for " ^ F.show k ^
          ". Previous declaration: " ^ Loc.show otherloc)
      else
        Some x) m1 m2 in
      m

  let merge_types t1 t2 =
    F.Map.union (fun _ l1 l2 -> Some (ScopeTypeExpressionUniqueList.merge l1 l2)) t1 t2

  let merge_kinds t1 t2 =
      F.Map.union (fun f (k,loc1 as kdecl) (k',loc2) ->
        if k == k' then Some kdecl
        else error ~loc:loc2 ("Duplicate kind declaration for " ^ F.show f ^ ". Previously declared in " ^ Loc.show loc1);
        ) t1 t2

  let merge_type_abbrevs m1 m2 = m1 @ m2

  let merge_toplevel_macros otlm toplevel_macros =
    F.Map.union (fun k (m1,l1) (m2,l2) ->
      if ScopedTerm.equal ~types:false m1 m2 then Some (m1,l1) else
        error ~loc:l2 (Format.asprintf "@[<v>Macro %a declared twice.@;@[<hov 2>%a @[%a@]@]@;@[<hov 2>%a @[%a@]@]@]" F.pp k Loc.pp l1 ScopedTerm.pretty m1 Loc.pp l2 ScopedTerm.pretty m2)
      ) otlm toplevel_macros
      

  let rec compile_block kinds types type_abbrevs clauses chr pred_subst ty_subst = function
    | [] -> kinds, types, type_abbrevs, clauses, chr
    | Scoped.Shorten(shorthands, { kinds = k; types = t; type_abbrevs = ta; body; pred_symbols = _; ty_symbols = _ }) :: rest ->
      let inpsubst = push_subst_shorthands shorthands pred_subst in
      let intysubst = push_subst_shorthands shorthands ty_subst in
      let kinds = merge_kinds (apply_subst_kinds intysubst k) kinds in
      let types = merge_types (apply_subst_types intysubst t) types in
      let type_abbrevs = merge_type_abbrevs type_abbrevs (apply_subst_type_abbrevs intysubst ta) in
      let kinds, types, type_abbrevs, clauses, chr =
        compile_block kinds types type_abbrevs clauses chr inpsubst intysubst body in
      compile_block kinds types type_abbrevs clauses chr pred_subst ty_subst rest
  | Scoped.Namespace (extra, { kinds = k; types = t; type_abbrevs = ta; body; pred_symbols = ps; ty_symbols = ts }) :: rest ->
      let new_pred_subst = push_subst extra ps pred_subst in
      let new_ty_subst = push_subst extra ts ty_subst in
      let kinds = merge_kinds (apply_subst_kinds new_ty_subst k) kinds in
      (* Format.eprintf "@[<v>Types before:@ %a@]@," F.Map.(pp ScopeTypeExpressionUniqueList.pretty) t; *)
      let types = merge_types (apply_subst_types new_ty_subst t) types in
      (* Format.eprintf "@[<v>Types after:@ %a@]@," F.Map.(pp ScopeTypeExpressionUniqueList.pretty) (apply_subst_types new_ty_subst t); *)
      let type_abbrevs = merge_type_abbrevs type_abbrevs (apply_subst_type_abbrevs new_ty_subst ta) in
      let kinds, types, type_abbrevs, clauses, chr =
        compile_block kinds types type_abbrevs clauses chr new_pred_subst new_ty_subst body in
      compile_block kinds types type_abbrevs clauses chr pred_subst ty_subst rest
  | Scoped.Clauses cl :: rest ->
      let cl = apply_subst_clauses pred_subst ty_subst cl in
      let clauses = cl :: clauses in
      compile_block kinds types type_abbrevs clauses chr pred_subst ty_subst rest
  | Scoped.Constraints (ch, { kinds = k; types = t; type_abbrevs = ta; body }) :: rest ->
      let kinds = merge_kinds (apply_subst_kinds ty_subst k) kinds in
      let types = merge_types (apply_subst_types ty_subst t) types in
      let type_abbrevs = merge_type_abbrevs type_abbrevs (apply_subst_type_abbrevs ty_subst ta) in
      (* let modes = merge_modes (apply_subst_modes subst m) modes in *)
      let chr = apply_subst_chrs pred_subst  ty_subst ch :: chr in
      let kinds, types, type_abbrevs, clauses, chr =
        compile_block kinds types type_abbrevs clauses chr pred_subst ty_subst body in
      compile_block kinds types type_abbrevs clauses chr pred_subst ty_subst rest
  | Scoped.Accumulated { kinds=k; types = t; type_abbrevs = ta; body; ty_symbols = _ } :: rest ->
      let kinds = merge_kinds (apply_subst_kinds ty_subst k) kinds in
      let types = merge_types (apply_subst_types ty_subst t) types in
      let type_abbrevs = merge_type_abbrevs type_abbrevs (apply_subst_type_abbrevs ty_subst ta) in
      let kinds, types, type_abbrevs, clauses, chr =
        compile_block kinds types type_abbrevs clauses chr ty_subst pred_subst body in
      compile_block kinds types type_abbrevs clauses chr ty_subst pred_subst rest

  let compile_body { Scoped.kinds; types; type_abbrevs; ty_symbols = _; pred_symbols = _; body } =
    compile_block kinds types type_abbrevs [] [] empty_subst empty_subst body

  let run state { Scoped.pbody; toplevel_macros } =
    let kinds, types, type_abbrevs, clauses_rev, chr_rev = compile_body pbody in
    let signature = { Flat.kinds; types; type_abbrevs; toplevel_macros } in
    { Flat.clauses = List.(flatten (rev clauses_rev)); chr = List.rev chr_rev; builtins = []; signature } (* TODO builtins can be in a unit *)


end

(* This is marshalable *)

module Check : sig

  val check : flags:flags -> State.t -> base:Assembled.program -> unchecked_compilation_unit -> checked_compilation_unit

end = struct

  let check_signature ~flags (base_signature : Assembled.signature) (signature : Flat.unchecked_signature) : Assembled.signature * Assembled.signature * float * Type_checker.typing_env =
    let { Assembled.kinds = ok; types = ot; type_abbrevs = ota; toplevel_macros = otlm } = base_signature in
    
    let { Flat.kinds; types; type_abbrevs; toplevel_macros } = signature in

    let all_kinds = Flatten.merge_kinds ok kinds in
    let check_k_begin = Unix.gettimeofday () in
    let all_type_abbrevs, type_abbrevs =
      List.fold_left (fun (all_type_abbrevs,type_abbrevs) (name, scoped_ty) ->
        (* TODO check disjoint from kinds *)
        let loc = scoped_ty.ScopedTypeExpression.loc in
        let _, _, { Type_checker.ty } = Type_checker.check_type ~type_abbrevs:all_type_abbrevs ~kinds:all_kinds scoped_ty in
        if F.Map.mem name all_type_abbrevs then begin
          let sk, otherloc = F.Map.find name all_type_abbrevs in
          if TypeAssignment.compare_skema sk ty <> 0 then
          error ~loc
            ("Duplicate type abbreviation for " ^ F.show name ^
              ". Previous declaration: " ^ Loc.show otherloc)
        end;
        F.Map.add name (ty,loc) all_type_abbrevs, F.Map.add name (ty,loc) type_abbrevs)
        (ota,F.Map.empty) type_abbrevs in
    let check_k_end = Unix.gettimeofday () in

    (* Type checking *)
    let check_t_begin = Unix.gettimeofday () in
    (* Type_checker.check_disjoint ~type_abbrevs ~kinds; *)

    let types = Type_checker.check_types ~type_abbrevs:all_type_abbrevs ~kinds:all_kinds types in


    (* let rec is_arrow_to_prop = function
      | ScopedTypeExpression.Lam (_,x) -> is_arrow_to_prop x
      | Ty t -> ScopedTypeExpression.is_prop t.it <> None in 

    let rec type2type_idx = function
      | [] -> []
      | x :: xs when is_arrow_to_prop x.ScopedTypeExpression.value ->
        x :: type2type_idx xs
      | _ :: xs -> type2type_idx xs
    in *)

  
    let check_t_end = Unix.gettimeofday () in

    let all_types = Flatten.merge_type_assignments ot types in
    let all_toplevel_macros = Flatten.merge_toplevel_macros otlm toplevel_macros in

    { Assembled.kinds; types; type_abbrevs; toplevel_macros },
    { Assembled.kinds = all_kinds; types = all_types; type_abbrevs = all_type_abbrevs; toplevel_macros = all_toplevel_macros },
    (if flags.time_typechecking then check_t_end -. check_t_begin +. check_k_end -. check_k_begin else 0.0),
    types

  let check_and_spill_pred ~needs_spilling ~unknown ~type_abbrevs ~kinds ~types t =
    let unknown = Type_checker.check ~is_rule:true ~unknown ~type_abbrevs ~kinds ~types t ~exp:(Val (Prop Relation)) in
    unknown, if needs_spilling then Spilling.main ~types t else t

  let check_and_spill_chr ~unknown ~type_abbrevs ~kinds ~types r =
    let unknown = Type_checker.check_chr_rule ~unknown ~type_abbrevs ~kinds ~types r in
    let guard = Option.map (Spilling.main ~types) r.guard in
    let new_goal = Option.map (fun ({ Ast.Chr.conclusion } as x) -> { x with conclusion = Spilling.main ~types conclusion }) r.new_goal in
    unknown, { r with guard; new_goal }

  let check ~flags st ~base u : checked_compilation_unit =

    let signature, precomputed_signature, check_sig, new_types = check_signature ~flags base.Assembled.signature u.code.Flat.signature in

    let { version; code = { Flat.clauses; chr; builtins } } = u in
    let { Assembled.kinds; types; type_abbrevs; toplevel_macros } = precomputed_signature in

    let check_begin = Unix.gettimeofday () in

    (* returns unkown types + clauses without spilling *)
    let unknown, clauses = List.fold_left (fun (unknown,clauses) ({ Ast.Clause.body; loc; needs_spilling; attributes = { Ast.Structured.typecheck } } as clause) ->
      let unknown, body = 
        if typecheck then check_and_spill_pred ~needs_spilling ~unknown ~type_abbrevs ~kinds ~types body
        else unknown, body in
      (* Format.eprintf "The checked clause is %a@." ScopedTerm.pp body; *)
      (* if String.starts_with ~prefix:"File \"<" (Loc.show loc)  then Format.eprintf "The clause is %a@." ScopedTerm.pp body; *)
      let spilled = {clause with body; needs_spilling = false} in
      (* if typecheck then Mode_checker.check ~is_rule:true ~type_abbrevs ~kinds ~types spilled.body; *)

      let is_deterministic = typecheck && Determinacy_checker.check_clause ~types ~unknown ~type_abbrevs spilled.body in

      unknown, {spilled with is_deterministic } :: clauses) (F.Map.empty,[]) clauses in
    let clauses = List.rev clauses in

    let unknown, chr = List.fold_left (fun (unknown,chr_blocks) { Ast.Structured.clique; ctx_filter; rules; loc } ->
        let clique = List.map (Type_checker.check_pred_name ~types ~loc) clique in
        let ctx_filter = List.map (Type_checker.check_pred_name ~types ~loc) ctx_filter in
        let unknown, rules = map_acc (fun unknown -> check_and_spill_chr ~unknown ~type_abbrevs ~kinds ~types) unknown rules in
        (unknown, { Ast.Structured.clique; ctx_filter; rules; loc } :: chr_blocks)
      ) (unknown, []) chr in
    let chr = List.rev chr in

    Symbol.QMap.iter (fun k { Type_checker.indexing; ty } ->
      match SymbolMap.get_global_symbol base.Assembled.symbols k with
      | Some c ->
          if Builtins.is_declared base.Assembled.builtins c then
            error ~loc:(Symbol.get_loc k)
              (Format.asprintf "Ascribing a type to an already registered builtin %s" (Symbol.get_str k))
      | _ -> ()) new_types.symbols;

    let builtins = List.map (fun (BuiltInPredicate.Pred(name,_,_) as p) ->
      let symb =
        match F.Map.find (F.from_string name) new_types.overloading with
        | Single s -> s
        | Overloaded (s1::s2::_) ->
            error ~loc:(Symbol.get_loc s2)
              (Format.asprintf "Multiple signatures for builtin %s\nOther signature: %a" name Symbol.pp s1);
        | Overloaded _ -> assert false
        | exception Not_found ->
            error (Format.asprintf "No signature declared for builtin %s" name) in
      let { Type_checker.indexing } = Symbol.QMap.find symb new_types.symbols in
      begin match indexing with
        | Type_checker.External None -> ()
        | _ -> error ~loc:(Symbol.get_loc symb) (Format.asprintf "Non external type declaration for builtin %s" name)
      end;
      symb, p
    ) builtins in

    let more_types = Type_checker.check_undeclared ~unknown in
    let u_types = Flatten.merge_type_assignments signature.types more_types in
    let types = Flatten.merge_type_assignments types more_types in

    let check_end = Unix.gettimeofday () in

    let signature = { signature with types = u_types } in
    let precomputed_signature = { precomputed_signature with types } in

    let checked_code = { CheckedFlat.signature; clauses; chr; builtins } in

  { version; checked_code; base_hash = hash_base base;
    precomputed_signature;
    type_checking_time = if flags.time_typechecking then check_end -. check_begin +. check_sig else 0.0 }

end


let todopp name _fmt _ = error ("pp not implemented for field: "^name)

let get_argmap, set_argmap, _update_argmap =
  let argmap =
    State.declare
      ~name:"elpi:argmap" ~pp:(todopp "elpi:argmap")
      ~descriptor:D.elpi_state_descriptor
      ~clause_compilation_is_over:(fun _ -> F.Map.empty)
      ~compilation_is_over:(fun _ -> None)
      ~execution_is_over:(fun _ -> None)
     ~init:(fun () -> F.Map.empty)
    () in
  State.(get argmap, set argmap, update_return argmap)
  
module Assemble : sig

  val extend : flags -> State.t -> Assembled.program -> checked_compilation_unit -> State.t * Assembled.program
  val extend_signature : State.t -> Assembled.program -> checked_compilation_unit_signature -> State.t * Assembled.program

  (* for the query *)
  val compile_query : State.t -> Assembled.program -> bool * ScopedTerm.t -> SymbolMap.table * int F.Map.t * D.term
  val compile_query_term :
    State.t -> Assembled.program ->
    ?ctx:constant Scope.Map.t ->
    ?amap:constant F.Map.t ->
    depth:int -> ScopedTerm.t -> constant F.Map.t * D.term

end = struct

  let update_indexing state symbols ({ idx } as index) (preds : (Symbol.t * _) list) old_idx =
    (* let check_if_some_clauses_already_in ~loc predicate c oldi newi =
         if Ptmap.mem c idx then
           error ~loc @@ "Some clauses for " ^ predicate ^
             " are already in the program, changing the indexing a posteriori is not allowed. " ^
             show_indexing oldi ^ " <> " ^ show_indexing newi
      in *)
      let check_if_some_clauses_already_in2 ~loc predicate c =
        if Ptmap.mem c idx then
          error ~loc @@ "2 Some clauses for " ^ predicate ^
            " are already in the program, changing the indexing a posteriori is not allowed."
     in

    let add_indexing_for name loc c index map =
      (* Format.eprintf "indexing for %s with id %a at pos %a\n%!" name pp_int c Loc.pp loc; *)
      (* Format.eprintf "its indexing is %a@." pp_indexing index; *)
      try
        let old_tindex =
          try C.Map.find c map
          with Not_found -> C.Map.find c old_idx in
        if old_tindex <> index then
            error ("multiple and inconsistent indexing attributes for " ^ name)
        else map
      with Not_found ->
          check_if_some_clauses_already_in2 ~loc name c;
          C.Map.add c index map
        in

    let map =
      preds |> List.fold_left (fun acc (symb,indexing) ->
        match SymbolMap.get_global_symbol symbols symb with
        | None -> assert false
        | Some c -> add_indexing_for (Symbol.get_str symb) (Symbol.get_loc symb) c indexing acc)
      C.Map.empty in
    R.CompileTime.update_indexing map index, C.Map.union (fun _ a b -> assert (a=b); Some a) map old_idx

    let lookup_global types symb state s =
      let c = Symbol.UF.find (Symbol.QMap.get_uf types.Type_checker.symbols) s in
      (* Format.eprintf "LOOKUP %a\n" Symbol.pp c; *)
      match SymbolMap.get_global_symbol !symb c with
      | None ->
      (* Format.eprintf " NEW\n"; *)
      let s, rc = SymbolMap.allocate_global_symbol state !symb s in
      symb := s;
      rc
     | Some c ->
      (* Format.eprintf "  FOUND %b\n" (is_builtin_predicate c); *)
        c, SymbolMap.get_canonical state !symb c

    let allocate_global_symbol types symb state ~loc s c =
      lookup_global types symb state @@
        match s with
        | Some s -> s
        | None -> 
          match F.Map.find c types.Type_checker.overloading with
          | TypeAssignment.Single s -> s
          | TypeAssignment.Overloaded _ ->
              error ~loc ("untyped and non allocated symbol " ^ F.show c)
          | exception Not_found ->
              error ~loc ("untyped and non allocated symbol " ^ F.show c)

  let to_dbl ?(ctx=Scope.Map.empty) ~types ~builtins state symb ?(depth=0) ?(amap = F.Map.empty) t =
    (* Format.eprintf "todbl: term : %a" ScopedTerm.pretty t; *)
    let symb = ref symb in
    let amap = ref amap in
    let allocate_arg c =
      try F.Map.find c !amap
      with Not_found ->
        let n = F.Map.cardinal !amap in
        amap := F.Map.add c n !amap;
        n in
    let lookup_bound loc (_,ctx) (c,l as x) =
      try Scope.Map.find x ctx
      with Not_found -> error ~loc ("Unbound variable " ^ F.show c ^ if l <> elpi_language then " (language: "^l^")" else "") in
    let allocate_bound_symbol loc ctx f =
      let c = lookup_bound loc ctx f in
      let s, rc = SymbolMap.allocate_bound_symbol state !symb c in
      symb := s;
      rc in
    let allocate_global_symbol = allocate_global_symbol types symb state in
    let push_bound (n,ctx) c = (n+1,Scope.Map.add c n ctx) in
    let push_unnamed_bound (n,ctx) = (n+1,ctx) in
    let push ctx : string ScopedTerm.ty_name option -> 'a = function
      | None -> push_unnamed_bound ctx
      | Some (l,x,_) -> push_bound ctx (x,l) in
    let open ScopedTerm in
    let rec todbl (ctx : int * _ Scope.Map.t) t =
      match t.it with
      | Impl(b,t1,t2) ->
          D.mkBuiltin (if b then Impl else RImpl) [todbl ctx t1;todbl ctx t2]
      | CData c -> D.mkCData (CData.hcons c)
      | Spill(t,_) ->
          error ~loc:t.loc (Format.asprintf "todbl: term contains spill: %a" ScopedTerm.pretty t)
      | Cast(t,_) -> todbl ctx t
      (* lists *)
      | Const(Global _,c,_) when F.(equal c nilf) -> D.mkNil
      | App((Global _,c,_),x,[y]) when F.(equal c consf) ->
          let x = todbl ctx x in
          let y = todbl ctx y in
          D.mkCons x y
      (* globals and builtins *)
      | Const((Global { decl_id },c,_)) ->
          let c, t = allocate_global_symbol ~loc:t.loc decl_id c in
          if is_builtin_predicate c then D.mkBuiltin (builtin_predicate_of_const c) []
          else if Builtins.is_declared builtins c then D.mkBuiltin (Host c) []
          else t
      | App((Global { decl_id },c,_),x,xs) ->
          let c,_ = allocate_global_symbol ~loc:t.loc decl_id c in
          let x = todbl ctx x in
          let xs = List.map (todbl ctx) xs in
          if is_builtin_predicate c then D.mkBuiltin (builtin_predicate_of_const c) (x::xs)
          else if Builtins.is_declared builtins c then D.mkBuiltin (Host c) (x::xs)
          else D.mkApp c x xs
      (* lambda terms *)
      | Const(Bound l,c,_) -> allocate_bound_symbol t.loc ctx (c,l)
      | Lam(c,_,t) -> D.mkLam @@ todbl (push ctx c) t
      | App((Bound l,c,_),x,xs) ->
          let c = lookup_bound t.loc ctx (c,l) in
          let x = todbl ctx x in
          let xs = List.map (todbl ctx) xs in
          D.mkApp c x xs
      (* holes *)
      | Var((_,c,_),xs) ->
          let xs = List.map (todbl ctx) xs in
          R.mkAppArg (allocate_arg c) 0 xs
      | Discard -> D.mkDiscard
    in

  let t  = todbl (depth,ctx) t in
  (!symb, !amap), t

  let spill_todbl ?(ctx=Scope.Map.empty) ~builtins ~needs_spilling ~types state symb ?(depth=0) ?(amap = F.Map.empty) t =
    let t = if needs_spilling then Spilling.main ~types t else t in
    to_dbl ~ctx ~builtins state symb ~types ~depth ~amap t

  let extend1_clause flags state indexing ~builtins ~types (clauses, symbols, index) { Ast.Clause.body; loc; needs_spilling; attributes = { Ast.Structured.insertion = graft; id; ifexpr }; is_deterministic } =
    assert (not needs_spilling);
    if not @@ filter1_if flags (fun x -> x) ifexpr then
      (clauses,symbols, index)
    else
    let (symbols, amap), body = to_dbl ~builtins ~types state symbols body in
    (* Format.eprintf "FINAL %a\n" (R.Pp.ppterm 0 [] ~argsdepth:0 empty_env) body;
    Format.eprintf "FINAL %a\n" (R.Pp.uppterm 0 [] ~argsdepth:0 empty_env) body; *)
    let modes x = Constants.Map.find_opt x indexing |> Option.map fst |> Option.value ~default:[] in
    let (p,cl), _, morelcs =
      try R.CompileTime.clausify1 ~loc ~modes ~nargs:(F.Map.cardinal amap) ~depth:0 body
      with D.CannotDeclareClauseForBuiltin(loc,_c) ->
        error ?loc ("Declaring a clause for built in predicate")
      in
    if morelcs <> 0 then error ~loc "sigma in a toplevel clause is not supported";

    let index = R.CompileTime.add_to_index ~depth:0 ~predicate:p ~graft cl id index in

    if is_deterministic then (
      let hd_query p { args; mode } =
        let rec mkpats args mode =
          match args, mode with
          | [], [] -> []
          | a::args, (Mode.Fo Input | Ho(Input,_)) :: mode -> a :: mkpats args mode
          | _::args, _ :: mode -> mkDiscard :: mkpats args mode
          | _::args, [] -> warn ~loc ("args/mode mismatch: " ^ String.concat " " (List.map  show_term args) ^ " != " ^ Mode.show_hos mode); mkDiscard :: mkpats args mode
          | _ -> assert false
        in
        R.mkAppL p @@ mkpats args mode in
      let valid_clause (cl : clause) =
        let overlapping = R.CompileTime.get_clauses ~check_mut_excl:true ~depth:0 p (hd_query p cl) index in
        let rec has_bang (t : term list) : bool =
          match t with
          | [] -> false
          | Builtin (Cut, []) :: _ -> true
          | Builtin (Pi, [Lam b]) :: xs | Builtin (Sigma, [Lam b]) :: xs -> has_bang [b] || has_bang xs
          | Builtin (Impl, [_; l]) :: xs -> has_bang [l] || has_bang xs
          | Builtin (And, l) :: xs -> has_bang l || has_bang xs
          | _ :: xs -> has_bang xs
        in
        let rec check_overlaps = function
          | [] -> assert false
          | x::xs when Option.equal Loc.equal x.Data.loc (Some loc) ->
              if (xs = [] || has_bang x.hyps) then []
              else xs
          | x::xs -> 
            if not (has_bang x.hyps) then (x::check_overlaps xs)
            else check_overlaps xs
        in
      let overlaps = check_overlaps (Bl.to_list overlapping) in
      if overlaps <> [] then
        let to_str = List.map (fun e -> Format.asprintf "overlaps with %s --> %a" 
          (Option.value ~default:"anonymous clause" (Option.map Loc.show e.loc)) (pplist pp_term ", ") e.hyps) overlaps  in
        error ~loc (Format.asprintf "- %s@." (String.concat  "\n - " to_str))
      in valid_clause cl
    );

    (graft,id,p,cl) :: clauses, symbols, index


  let check_rule_pattern_in_clique state symbols clique { D.CHR.pattern; rule_name; rule_loc } =
    try
      let outside =
        List.find (fun x -> not (D.CHR.in_clique clique x)) pattern in
      error ~loc:rule_loc ("CHR rule " ^ rule_name ^ ": matches " ^ (F.show @@ SymbolMap.global_name state symbols outside) ^
        " which is not a constraint on which it is applied. Check the list of predicates after the \"constraint\" keyword.");
    with Not_found -> ()
    
  let extend1_chr flags state clique ~builtins ~types (symbols,chr) { Ast.Chr.to_match; to_remove; guard; new_goal; attributes; loc } =
    if not @@ filter1_if flags (fun x -> x.Ast.Structured.cifexpr) attributes then
      (symbols,chr)
    else
    let todbl state (symbols,amap) t = to_dbl ~types ~builtins state symbols ~amap t in
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

  let extend1_chr_block flags state ~builtins ~types (symbols,chr) { Ast.Structured.clique; ctx_filter; rules; loc } =
    let allocate_global_symbol state symbols f =
      let symbols = ref symbols in
      let (c,_) = allocate_global_symbol types symbols state ~loc (Some f) (Symbol.get_func f) in
      !symbols, c in
    let symbols, clique = map_acc (allocate_global_symbol state) symbols clique in
    let symbols, ctx_filter = map_acc (allocate_global_symbol state) symbols ctx_filter in
    let chr, clique = CHR.new_clique (SymbolMap.global_name state symbols) ctx_filter clique chr in
    List.fold_left (extend1_chr ~builtins ~types flags state clique) (symbols,chr) rules

let extend1_signature base_signature (signature : checked_compilation_unit_signature) =
  let { Assembled.kinds = ok; types = ot; type_abbrevs = ota; toplevel_macros = otlm } = base_signature in
  let { Assembled.toplevel_macros; kinds; types; type_abbrevs } = signature in
  let kinds = Flatten.merge_kinds ok kinds in
  let type_abbrevs = Flatten.merge_checked_type_abbrevs ota type_abbrevs in
  let types = Flatten.merge_type_assignments ot types in
  let toplevel_macros = Flatten.merge_toplevel_macros otlm toplevel_macros in

  { Assembled.kinds; types; type_abbrevs; toplevel_macros }

let extend1 flags (state, base) unit =

  let signature =
    if hash_base base = unit.base_hash
    then unit.precomputed_signature
    else extend1_signature base.Assembled.signature unit.checked_code.CheckedFlat.signature in

  let { Assembled.hash; clauses = cl; symbols; prolog_program; indexing; signature = bsig; chr = ochr; builtins = ob; total_type_checking_time } = base in
  let { version; base_hash; checked_code = { CheckedFlat.clauses; chr; builtins; signature = { types = new_types } }; type_checking_time; } = unit in

  (* Format.eprintf "extend %a\n%!" (F.Map.pp (fun _ _ -> ())) types_indexing; *)
  
  let new_defined_symbols, new_indexable =
    let symbs = Symbol.QMap.bindings new_types.symbols in
    symbs |> List.filter_map (fun (symb,_) -> if Symbol.QMap.mem symb bsig.types.symbols then None else Some symb),
    symbs |> List.filter_map (fun (symb, { Type_checker.indexing } ) -> match indexing with Index(m,i) -> Some (symb,(m,i)) | _ -> None) in

  let symbols =
    (* THE MISTERY: allocating symbols following their declaration order makes the grundlagen job 30% faster (600M less memory):
            time   typchk wall   mem
      with: 14.75   0.53  16.69 2348.4M
      wout: 19.61   0.56  21.72 2789.1M 
    *)
    let new_defined_symbols =
      if List.length new_defined_symbols > 2000 then
        new_defined_symbols |> List.sort (fun s1 s2 -> compare (Symbol.get_loc s1).line (Symbol.get_loc s2).line)
      else
        new_defined_symbols in
    List.fold_left (fun symbols s -> SymbolMap.allocate_global_symbol state symbols s |> fst)
      symbols new_defined_symbols in

  let prolog_program, indexing = update_indexing state symbols prolog_program new_indexable indexing in
  (* Format.eprintf "extended\n%!"; *)

  let symbols, builtins =
    List.fold_left (fun (symbols,builtins) (symb, p) ->
      let symbols, (c,_) = SymbolMap.allocate_global_symbol state symbols symb in
      let builtins = Builtins.register builtins p c in
      symbols, builtins) (symbols, ob) builtins in

  let symbols, chr =
    List.fold_left (extend1_chr_block ~builtins ~types:signature.types flags state) (symbols,ochr) chr in

  let clauses, symbols, prolog_program =
    (* TODO: pass also typeabbrevs *)
    List.fold_left (extend1_clause ~builtins ~types:signature.types flags state indexing) (cl, symbols, prolog_program) clauses in

  (* Printf.eprintf "kinds: %d\n%!" (F.Map.cardinal kinds); *)

  let total_type_checking_time = total_type_checking_time +. type_checking_time in

  let base = { Assembled.builtins; hash; symbols; chr; clauses; prolog_program; signature; indexing; total_type_checking_time } in
  let hash = hash_base base in
  state, { base with hash }

  let extend flags state assembled u = extend1 flags (state, assembled) u
  let extend_signature state assembled u =
    let signature = extend1_signature assembled.Assembled.signature u in
    let base = { assembled with signature } in
    state, { base with hash = hash_base base }

  let compile_query state { Assembled.symbols; builtins; signature = { types } } (needs_spilling,t) =
    let (symbols, amap), t = spill_todbl ~builtins ~needs_spilling ~types state symbols t in
    symbols, amap, t 

  let compile_query_term state { Assembled.symbols; builtins; signature = { types } } ?ctx ?(amap = F.Map.empty) ~depth t =
    let (symbols', amap), rt = spill_todbl ~builtins ?ctx ~needs_spilling:false state symbols ~types ~depth ~amap t in
    if SymbolMap.equal_globals symbols' symbols then amap, rt
    else error ~loc:t.ScopedTerm.loc "cannot allocate new symbols in the query"

end


(****************************************************************************
  API
 ****************************************************************************)

let scope s ~toplevel_macros p : scoped_program =
  let p = RecoverStructure.run s p in
  let p = Scope_Quotation_Macro.run ~toplevel_macros s p in
  {
    version = "%%VERSION_NUM%%";
    code = p;
  }

(* Compiler passes *)
let unit_or_header_of_scoped s ~builtins (p : scoped_program) : unchecked_compilation_unit =
  assert ("%%VERSION_NUM%%" = p.version);
  let p = Flatten.run s p.code in
  {
    version = "%%VERSION_NUM%%";
    code = { p with builtins };
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
  let builtins =
    List.flatten @@
    List.map (fun (_,decl) -> decl |> List.filter_map (function
      | Data.BuiltInPredicate.MLCode (p,_) -> Some p
      | _ -> None)) builtins in
  let scoped_ast = scope ~toplevel_macros:F.Map.empty state ast in
  let u = unit_or_header_of_scoped state ~builtins scoped_ast in
  print_unit flags u;
  let base = Assembled.empty () in
  let u = Check.check ~flags state ~base u in
 (* with toplevel_macros = u.checked_code.signature.toplevel_macros } in *)
  (* Printf.eprintf "header_of_ast: types u %d\n%!" (F.Map.cardinal u.checked_code.CheckedFlat.signature.types); *)
  let h = assemble_unit ~flags ~header:(state,base) u in
  (* Printf.eprintf "header_of_ast: types h %d\n%!" (F.Map.cardinal (snd h).Assembled.signature.types); *)
  h

let check_unit ~flags ~base:(st,base) u = Check.check ~flags st ~base u

let empty_base ~header:b = b

let scoped_of_ast ~flags:_ ~header:(s,u) p =
  scope ~toplevel_macros:u.Assembled.signature.toplevel_macros s p

let unit_of_scoped ~flags ~header:(s, u) ?(builtins=[]) p : unchecked_compilation_unit =
  let builtins =
    List.flatten @@
    List.map (fun (_,decl) -> decl |> List.filter_map (function
      | Data.BuiltInPredicate.MLCode (p,_) -> Some p
      | _ -> error "Only BuiltInPredicate.MLCode allowed in units")) builtins in
  let u = unit_or_header_of_scoped s ~builtins p in
  print_unit flags u;
  u

let append_unit ~flags ~base:(s,p) unit : program =
  Assemble.extend flags s p unit

let append_unit_signature ~flags ~base:(s,p) unit : program =
  Assemble.extend_signature s p unit
  
let program_of_ast ~flags ~header:((st, base) as header : State.t * Assembled.program) p : program =
  let p = scoped_of_ast ~flags ~header p in
  let u = unit_of_scoped ~flags ~header p in
  let u = Check.check ~flags st ~base u in
  assemble_unit ~flags ~header u

let total_type_checking_time { WithMain.total_type_checking_time = x } = x

let pp_uvar_body fmt ub = R.Pp.uppterm 0 [] ~argsdepth:0 [||] fmt (D.mkUVar ub 0 0)
let pp_uvar_body_raw fmt ub = R.Pp.ppterm 0 [] ~argsdepth:0 [||] fmt (D.mkUVar ub 0 0)
  
let uvk = D.State.declare ~descriptor:D.elpi_state_descriptor ~name:"elpi:uvk" ~pp:(Util.StrMap.pp pp_uvar_body)
    ~clause_compilation_is_over:(fun x -> Util.StrMap.empty)
    ~compilation_is_over:(fun x -> Some x)
    ~execution_is_over:(fun _ -> None)
    ~init:(fun () -> Util.StrMap.empty)
    ()

let compile_builtins b = 
  let builtins = Hashtbl.create 17 in
  let () = Builtins.fold (fun c p () -> Hashtbl.add builtins c p) b () in
  builtins

let query_of_ast (compiler_state, assembled_program) t state_update =
  let compiler_state = State.begin_goal_compilation compiler_state in
  let { Assembled.signature = { kinds; types; type_abbrevs; toplevel_macros; }; chr; prolog_program; total_type_checking_time } = assembled_program in
  let total_type_checking_time = assembled_program.Assembled.total_type_checking_time in
  let needs_spilling = ref false in
  let t = Scope_Quotation_Macro.scope_loc_term ~state:(set_mtm compiler_state { empty_mtm with macros = toplevel_macros; needs_spilling }) t in
  let unknown = Type_checker.check ~is_rule:false ~unknown:F.Map.empty ~type_abbrevs ~kinds ~types t ~exp:TypeAssignment.(Val (Prop Relation)) in
  let _ = Type_checker.check_undeclared ~unknown in
  let symbols, amap, query = Assemble.compile_query compiler_state assembled_program (!needs_spilling,t) in
  let query_env = Array.make (F.Map.cardinal amap) D.dummy in
  let initial_goal = R.move ~argsdepth:0 ~from:0 ~to_:0 query_env query in
  let assignments = F.Map.fold (fun k i m -> StrMap.add (F.show k) query_env.(i) m) amap StrMap.empty in
  let assignments = StrMap.fold (fun k i m -> StrMap.add k (UVar(i,0,0)) m) (State.get uvk compiler_state) assignments in
  let builtins = assembled_program.Assembled.builtins in
  {
    WithMain.prolog_program;
    chr;
    symbols;
    initial_goal;
    assignments;
    compiler_state = compiler_state |> state_update;
    total_type_checking_time;
    builtins;
  }

let compile_term_to_raw_term ?(check=true) state (_, assembled_program) ?ctx ~depth t =
  if not @@ State.get Data.while_compiling state then
    anomaly "compile_term_to_raw_term called at run time";
  let { Assembled.signature = { kinds; types; type_abbrevs }; chr; prolog_program; total_type_checking_time } = assembled_program in
  if check && Option.fold ~none:true ~some:Scope.Map.is_empty ctx then begin
    let unknown = Type_checker.check ~is_rule:false ~unknown:F.Map.empty ~type_abbrevs ~kinds ~types t ~exp:(Type_checker.unknown_type_assignment "Ty") in
    let _ : Type_checker.typing_env = Type_checker.check_undeclared ~unknown in
    ()
  end;
  let amap = get_argmap state in
  let amap, t = Assemble.compile_query_term ?ctx ~amap state assembled_program ~depth t in
  set_argmap state amap,t

let runtime_hack_term_to_raw_term state (_, assembled_program) ?ctx ~depth t =
  if State.get Data.while_compiling state then
    anomaly "runtime_hack_term_to_raw_term called at compile time";
  let amap, t = Assemble.compile_query_term ?ctx state assembled_program ~depth t in
  if F.Map.is_empty amap then t
  else 
    let query_env = Array.make (F.Map.cardinal amap) D.dummy in
    R.move ~argsdepth:depth ~from:depth ~to_:depth query_env t
        

let query_of_scoped_term (compiler_state, assembled_program) f =
  let compiler_state = State.begin_goal_compilation compiler_state in
  let { Assembled.signature = { kinds; types; type_abbrevs }; chr; prolog_program; total_type_checking_time } = assembled_program in
  let total_type_checking_time = assembled_program.Assembled.total_type_checking_time in
  let compiler_state,t = f compiler_state in
  let unknown = Type_checker.check ~is_rule:false ~unknown:F.Map.empty ~type_abbrevs ~kinds ~types t ~exp:TypeAssignment.(Val (Prop Relation)) in
  let _ = Type_checker.check_undeclared ~unknown in
  let symbols, amap, query = Assemble.compile_query compiler_state assembled_program (false,t) in
  let query_env = Array.make (F.Map.cardinal amap) D.dummy in
  let initial_goal = R.move ~argsdepth:0 ~from:0 ~to_:0 query_env query in
  let assignments = F.Map.fold (fun k i m -> StrMap.add (F.show k) query_env.(i) m) amap StrMap.empty in
  let assignments = StrMap.fold (fun k i m -> StrMap.add k (UVar(i,0,0)) m) (State.get uvk compiler_state) assignments in
  let builtins = assembled_program.Assembled.builtins in
  {
    WithMain.prolog_program;
    chr;
    symbols;
    initial_goal;
    assignments;
    compiler_state;
    total_type_checking_time;
    builtins;
  }
    
  let query_of_raw_term (compiler_state, assembled_program) f =
    let compiler_state = State.begin_goal_compilation compiler_state in
    let { Assembled.signature = { kinds; types; type_abbrevs }; chr; prolog_program; total_type_checking_time } = assembled_program in
    let total_type_checking_time = assembled_program.Assembled.total_type_checking_time in
    let compiler_state, query, gls = f compiler_state in
    let compiler_state, gls = Data.State.get Data.Conversion.extra_goals_postprocessing compiler_state gls compiler_state in
    let gls = List.map Data.Conversion.term_of_extra_goal gls in
    let query =
      match gls @ [query] with
      | [] -> assert false
      | [g] -> g
      | x :: xs -> mkBuiltin And (x :: xs) in
    let amap = get_argmap compiler_state in
    let query_env = Array.make (F.Map.cardinal amap) D.dummy in
    let initial_goal = R.move ~argsdepth:0 ~from:0 ~to_:0 query_env query in
    let assignments = F.Map.fold (fun k i m -> StrMap.add (F.show k) query_env.(i) m) amap StrMap.empty in
    let assignments = StrMap.fold (fun k i m -> StrMap.add k (UVar(i,0,0)) m) (State.get uvk compiler_state) assignments in
    let builtins = assembled_program.Assembled.builtins in
    {
      WithMain.prolog_program;
      chr;
      symbols = assembled_program.Assembled.symbols;
      initial_goal;
      assignments;
      compiler_state;
      total_type_checking_time;
      builtins
    }
  
let symtab : (constant * D.term) Symbol.RawMap.t D.State.component = D.State.declare
  ~descriptor:D.elpi_state_descriptor
  ~name:"elpi:symbol_table"
  ~pp:(fun fmt _ -> Format.fprintf fmt "<symbol_table>")
  ~clause_compilation_is_over:(fun x -> x)
  ~compilation_is_over:(fun x -> Some x)
  ~execution_is_over:(fun _ -> None)
  ~init:(fun () -> Symbol.RawMap.empty)
  ()
  
let global_name_to_constant state s =
  let map = State.get symtab state in
  fst @@  Symbol.RawMap.find (Symbol.make_builtin (F.from_string s)) map

module Compiler : sig

  val run : query -> executable

end = struct (* {{{ *)


let run
  {
    WithMain.prolog_program;
    chr;
    symbols;
    initial_goal;
    assignments;
    builtins;
    compiler_state = state;
  }
=
  let symbol_table = SymbolMap.compile symbols in
  let state = State.set symtab state (SymbolMap.compile_s2c symbols) in
  {
    D.compiled_program = { index = close_index prolog_program; src = [] };
    chr;
    initial_depth = 0;
    initial_goal;
    initial_runtime_state = State.end_compilation state;
    assignments;
    symbol_table;
    builtins = compile_builtins builtins;
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

let pp_program (pp : pp_ctx:pp_ctx -> depth:int -> _) fmt (compiler_state, { Assembled.clauses; signature; symbols }) =

  let clauses = handle_clause_graftin clauses in

  let pp_ctx = {
    uv_names = ref (IntMap.empty, 0);
    table = SymbolMap.compile symbols;
  } in
  Format.fprintf fmt "@[<v>";
  F.Map.iter (fun name (ty,_) ->
    let rec a2k = function
      | 0 -> "type"
      | n -> "type -> " ^ a2k (n-1) in
    Format.fprintf fmt "@[<h>kind %s %s.@]@," (F.show name) (a2k ty))
    signature.kinds;
  F.Map.iter (fun name sl ->
    let f s = TypeAssignment.fresh (Symbol.QMap.find s signature.types.symbols).ty |> fst in
    let tys =
      match sl with
      | TypeAssignment.Single t -> [f t]
      | TypeAssignment.Overloaded l -> List.map f l in
    let name =
      match Elpi_parser.Parser_config.precedence_of (F.show name) with
      | (Some _,_) -> "("^F.show name^")"
      | _ -> F.show name in
    List.iter (fun ty ->
      Format.fprintf fmt "@[<h>type %s %a.@]@," name TypeAssignment.pretty_mut_once ty) tys;
    )
    signature.types.overloading;
  F.Map.iter (fun name (ty,_) ->
    Format.fprintf fmt "@[<h>typeabbrv %a (%a).@]@," F.pp name TypeAssignment.pretty_mut_once (fst @@ TypeAssignment.fresh ty)
    )
    signature.type_abbrevs;
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
    let s = Util.Constants.Map.find c symbol_table.c2s in
    let c = SymbolMap.get_global_symbol symbols s in
    match c with
    | Some x -> x
    | None -> raise (RelocationError (Format.asprintf "Relocation: unknown global %a" Symbol.pp s))
    in
  let rec rel = function
    | Const c when c < 0 -> Const (relocate c)
    | Const _ as x -> x
    | App(c,x,xs) when c < 0 -> App(relocate c,rel x,List.map rel xs)
    | App(c,x,xs) -> App(c,rel x, List.map rel xs)
    | Cons(x,y) -> Cons(rel x, rel y)
    | Lam t -> Lam(rel t)
    | CData _ as x -> x
    | Builtin(c,l) -> Builtin(map_builtin_predicate relocate c,List.map rel l)
    | (Nil | Discard) as x -> x
    | Arg _ | AppArg _ | UVar _ | AppUVar _ -> assert false
  in
    rel t
  
let relocate_closed_term ~from ~to_ t =
  try Result.Ok(relocate_closed_term ~from ~to_ t)
  with RelocationError s -> Result.Error s
