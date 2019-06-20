(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Util
module F = Ast.Func
module R = Runtime_trace_off

type flags = {
  defined_variables : StrSet.t;
  allow_untyped_builtin : bool;
  print_passes : bool;
}
[@@deriving show]

let default_flags = {
  defined_variables = StrSet.empty;
  allow_untyped_builtin = false;
  print_passes = false;
}

(****************************************************************************
  Intermediate data structures
 ****************************************************************************)

module StructuredAST = struct

open Ast

type program = {
  macros : (F.t, Ast.Term.t) Macro.t list;   
  types : tattribute Type.t list;
  modes : F.t Mode.t list;
  body : block list;
}
and block =
  | Locals of F.t list * program
  | Clauses of (Term.t,attribute) Clause.t list
  | Namespace of F.t * program
  | Shorten of F.t shorthand list * program
  | Constraints of F.t list * cattribute Chr.t list * program
and attribute = {
  insertion : insertion option;
  id : string option;
  ifexpr : string option;
}
and insertion = Before of string | After of string
and cattribute = {
  cid : string;
  cifexpr : string option
}
and tattribute =
  | External
  | Indexed of int list
and 'a shorthand = {
  iloc : Loc.t;
  full_name : 'a;
  short_name : 'a;
}
[@@deriving show]

end

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
  modes : mode C.Map.t;
  body : block list;
  (* defined (global) symbols (including in sub blocks) *)
  symbols : C.Set.t;
}
and block =
  | Clauses of (preterm,StructuredAST.attribute) Ast.Clause.t list
  | Namespace of string * pbody
  | Shorten of C.t StructuredAST.shorthand list * pbody
  | Constraints of constant list * prechr_rule list * pbody
and typ = {
  tindex : StructuredAST.tattribute;
  loc : Loc.t;
  decl : type_declaration
}
[@@deriving show]

end

module Flat = struct

type program = {
  types : Structured.typ list; 
  modes : mode C.Map.t;
  clauses : (preterm,StructuredAST.attribute) Ast.Clause.t list;
  chr : (constant list * prechr_rule list) list;
  local_names : int;

  toplevel_macros : macro_declaration;
}
[@@deriving show]

end

module Assembled = struct

type program = {
  types : Structured.typ list; 
  modes : mode C.Map.t;
  clauses : (preterm,attribute) Ast.Clause.t list;
  chr : (constant list * prechr_rule list) list;
  local_names : int;

  toplevel_macros : macro_declaration;
}
and attribute = {
  id : string option;
  ifexpr : string option;
}
[@@deriving show]

end

module Compiled = struct

(* The entire program + stuff needed in order to run the query *)
type program = {
  assembled_program : Assembled.program;
  compiler_state : State.t;
  compiler_flags : flags;
}
[@@deriving show]
  
end
type program = Compiled.program

module WithMain = struct

(* The entire program + query, but still in "printable" format *)
type 'a query = {
  types : Structured.typ list; 
  modes : mode C.Map.t;
  clauses : (preterm,Assembled.attribute) Ast.Clause.t list;
  chr : (constant list * prechr_rule list) list;
  initial_depth : int;
  query : preterm;
  query_arguments : 'a Query.arguments [@opaque];
  (* We pre-compile the query to ease the API *)
  initial_goal : term; assignments : term StrMap.t;
  initial_state : State.t;
  compiler_flags : flags;
}
[@@deriving show]

end
type 'a query = 'a WithMain.query

module Executable = struct

(* All that is needed in order to execute, and nothing more *)
type 'a executable = 'a Data.executable = {
  (* the lambda-Prolog program: an indexed list of clauses *) 
  compiled_program : prolog_prog;
  (* chr rules *)
  chr : CHR.t;
  (* initial depth (used for both local variables and CHR (#eigenvars) *)
  initial_depth : int;
  (* query *)
  initial_goal: term;
  (* constraints coming from compilation *)
  initial_state : State.t;
  (* solution *)
  assignments : term StrMap.t;
  (* reified type of the query *)
  query_arguments : 'a Query.arguments;
}

end

(****************************************************************************
  Compiler
 ****************************************************************************)

module RecoverStructure : sig

  (* Reconstructs the structure of the AST (i.e. matches { with }) *)

  val run : flags:flags -> Ast.Program.t -> StructuredAST.program

end = struct (* {{{ *)
  
  open StructuredAST
  open Ast
 
  let cl2b = function
    | [] -> []
    | clauses -> [Clauses (List.rev clauses)]

  let structure_clause_attributes ({ Clause.attributes; loc } as c) =
    let duplicate_err s =
      error ~loc ("duplicate attribute " ^ s) in
    let rec aux r = function
      | [] -> r
      | Clause.Name s :: rest ->
         if r.id <> None then duplicate_err "name";
         aux { r with id = Some s } rest
      | Clause.After s :: rest ->
         if r.insertion <> None then duplicate_err "insertion";
         aux { r with insertion = Some (After s) } rest
      | Clause.Before s :: rest ->
         if r.insertion <> None then duplicate_err "insertion";
         aux { r with insertion = Some (Before s) } rest
      | Clause.If s :: rest ->
         if r.ifexpr <> None then duplicate_err "if";
         aux { r with ifexpr = Some s } rest
    in
    { c with Clause.attributes =
        aux { insertion = None; id = None; ifexpr = None } attributes }

  let structure_chr_attributes ({ Chr.attributes; loc } as c) =
    let duplicate_err s =
      error ~loc ("duplicate attribute " ^ s) in
    let rec aux r = function
      | [] -> r
      | Chr.Name s :: rest ->
         aux { r with cid = s } rest
      | Chr.If s :: rest ->
         if r.cifexpr <> None then duplicate_err "if";
         aux { r with cifexpr = Some s } rest
    in
    let cid = Loc.show loc in 
    { c with Chr.attributes = aux { cid; cifexpr = None } attributes }

  let structure_type_attributes ({ Type.attributes; loc } as c) =
    let duplicate_err s =
      error ~loc ("duplicate attribute " ^ s) in
    let rec aux r = function
      | [] -> r
      | Type.External :: rest ->
         begin match r with
           | None -> aux (Some External) rest
           | Some External -> duplicate_err "external"
           | Some _ -> error ~loc "external predicates cannot be indexed"
         end
      | Type.Index i :: rest ->
         begin match r with
           | None -> aux (Some (Indexed i)) rest
           | Some (Indexed _) -> duplicate_err "index"
           | Some _ -> error ~loc "external predicates cannot be indexed"
         end
    in
    let attributes = aux None attributes in
    let attributes =
      match attributes with
      | None -> Indexed [1]
      | Some x -> x in
    { c with Type.attributes }
               

  let run ~flags:_ dl =
    let rec aux blocks clauses macros types modes  locals chr = function
      | (Program.End _ :: _ | []) as rest ->
          { body = List.rev (cl2b clauses @ blocks);
            types = List.rev types;
            macros = List.rev macros;
            modes = List.rev modes },
          locals,
          List.rev chr,
          rest
      | Program.Begin loc :: rest ->
          let p, locals1, chr1, rest = aux [] [] [] [] [] [] [] rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside an anonymous block";
          aux_end_block loc (Locals(locals1,p) :: cl2b clauses @ blocks)
            [] macros types modes locals chr rest
      | Program.Constraint (loc, f) :: rest ->
          if chr <> [] then
            error "Constraint blocks cannot be nested";
          let p, locals1, chr, rest = aux [] [] [] [] [] [] [] rest in
          if locals1 <> [] then
            error "locals cannot be declared inside a Constraint block";
          aux_end_block loc (Constraints(f,chr,p) :: cl2b clauses @ blocks)
            [] macros types modes locals [] rest
      | Program.Namespace (loc, n) :: rest ->
          let p, locals1, chr1, rest = aux [] [] [] [] [] [] [] rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside a namespace block";
          if locals1 <> [] then
            error "locals cannot be declared inside a namespace block";
          aux_end_block loc (Namespace (n,p) :: cl2b clauses @ blocks)
            [] macros types modes locals chr rest
      | Program.Shorten (loc,full_name,short_name) :: rest ->
          let shorthand = { iloc = loc; full_name; short_name } in  
          let p, locals1, chr1, rest = aux [] [] [] [] [] [] [] rest in
          if locals1 <> [] then
            error "locals cannot be declared after a shorthand";
          if chr1 <> [] then
            error "CHR cannot be declared after a shorthand";
          aux ((Shorten([shorthand],p) :: cl2b clauses @ blocks))
            [] macros types modes locals chr rest

      | Program.Accumulated (loc,a) :: rest ->
          aux blocks clauses macros types modes locals chr
            (Program.Begin loc :: a @ Program.End loc :: rest)

      | Program.Clause c :: rest ->
          let c = structure_clause_attributes c in
          aux blocks (c::clauses) macros types modes locals chr rest
      | Program.Macro m :: rest ->
          aux blocks clauses (m::macros) types modes locals chr rest
      | Program.Type t :: rest ->
          let t = structure_type_attributes t in
          aux blocks clauses macros (t::types) modes locals chr rest
      | Program.Mode ms :: rest ->
          aux blocks clauses macros types (ms @ modes) locals chr rest
      | Program.Local l :: rest ->
          aux blocks clauses macros types modes (l::locals) chr rest
      | Program.Chr r :: rest ->
          let r = structure_chr_attributes r in
          aux blocks clauses macros types modes locals (r::chr) rest

    and aux_end_block loc blocks clauses macros types modes locals chr rest =
      match rest with
      | Program.End _ :: rest ->
          aux blocks clauses macros types modes locals chr rest
      | _ -> error ~loc "matching } is missing"

    in
    let blocks, locals, chr, rest = aux [] [] [] [] [] [] [] dl in
    assert(rest = []);
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

let while_compiling = State.declare ~name:"elpi:compiling"
  ~pp:(fun fmt _ -> ())
  ~compilation_is_over:(fun ~args:_ _ -> Some false)
  ~init:(fun () -> true)

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

  val run : flags:flags -> State.t -> StructuredAST.program -> State.t * Structured.program

  (* Exported since also used to flatten (here we "flatten" locals) *)
  val prefix_const : string list -> C.t -> C.t
  val merge_modes : mode Map.t -> mode Map.t -> mode Map.t
  val merge_types :
        Structured.typ list ->
        Structured.typ list ->
        Structured.typ list

  (* Exported to compile the query *)
  val preterm_of_ast :
    depth:int -> macro_declaration -> State.t ->
      Loc.t * Ast.Term.t -> State.t * preterm
  val preterm_of_function :
    depth:int -> macro_declaration -> State.t -> 
    (State.t -> State.t * (Loc.t * term)) ->
      State.t * preterm

  (* Exported for quations *)    
  val lp : quotation
  val is_Arg : State.t -> term -> bool
  val fresh_Arg : 
    State.t -> name_hint:string -> args:term list ->
      State.t * term
  val mk_Arg : State.t -> name:string -> args:term list -> State.t * term
  val get_Arg : State.t -> name:string -> args:term list -> term
  val get_Args : State.t -> term StrMap.t

end = struct (* {{{ *)


(* **** ast->term compiler state ***************************************** *) 

let get_argmap, set_argmap, update_argmap =
  let argmap =
    State.declare ~name:"elpi:argmap" ~pp:(todopp "elpi:argmap")
      ~compilation_is_over:(fun ~args:_ _ -> None)
     ~init:(fun () -> empty_amap) in
  State.(get argmap, set argmap, update_return argmap)

(* For bound variables *)
type varmap = term F.Map.t 

let get_varmap, set_varmap, update_varmap =
  let varmap =
    State.declare ~name:"elpi:varmap" ~pp:(todopp "elpi:varmap")
      ~compilation_is_over:(fun ~args:_ _ -> None)
      ~init:(fun () -> F.Map.empty) in
  State.(get varmap, set varmap, update varmap)

(* Embed in the state everything, to cross quotations *)

type mtm = {
  macros : macro_declaration;
}

let get_mtm, set_mtm =
  let mtm =
    State.declare ~name:"elpi:mtm" ~pp:(todopp "elpi:mtm")
      ~compilation_is_over:(fun ~args:_ _ -> None)
      ~init:(fun () -> None) in
  State.(get mtm, set mtm)

(**** utils ******************)

let is_Arg state x =
  let { c2i } = get_argmap state in
  match x with
  | Const c -> C.Map.mem c c2i
  | App(c,_,_) -> C.Map.mem c c2i
  | _ -> false

let mk_Arg state ~name ~args =
  let { n2t } = get_argmap state in
  let state, (t, c) =
    try state, StrMap.find name n2t
    with Not_found -> update_argmap state (mk_Arg name) in
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

let preterm_of_ast loc ~depth:arg_lvl macro state ast =

  let is_uvar_name f = 
     let c = (F.show f).[0] in
     ('A' <= c && c <= 'Z') in
    
  let is_discard f =
     let c = (F.show f).[0] in
     c = '_' in

  let is_macro_name f = 
     let c = (F.show f).[0] in
     c = '@' in


  let rec stack_macro_of_ast inner lvl state f =
    try aux inner lvl state (fst (F.Map.find f macro))
    with Not_found -> error ~loc ("Undeclared macro " ^ F.show f) 

  (* compilation of "functors" *) 
  and stack_funct_of_ast inner curlvl state f =
    try state, F.Map.find f (get_varmap state)
    with Not_found ->
     if is_discard f then
       state, Discard
     else if is_uvar_name f then
       mk_Arg state ~name:(F.show f) ~args:[]
     else if is_macro_name f then
       stack_macro_of_ast inner curlvl state f
     else if BuiltInPredicate.is_declared (fst (C.funct_of_ast f)) then
       state, Builtin(fst (C.funct_of_ast f),[])
     else if CustomFunctorCompilation.is_backtick f then
       CustomFunctorCompilation.compile_backtick state f
     else if CustomFunctorCompilation.is_singlequote f then
       CustomFunctorCompilation.compile_singlequote state f
     else state, snd (C.funct_of_ast f)
  
  and aux inner lvl state = function
    | Ast.Term.Const f when F.(equal f nilf) -> state, Term.Nil
    | Ast.Term.Const f -> stack_funct_of_ast inner lvl state f
    | Ast.Term.App(Ast.Term.Const f, [hd;tl]) when F.(equal f consf) ->
       let state, hd = aux true lvl state hd in
       let state, tl = aux true lvl state tl in
       state, Term.Cons(hd,tl)
    | Ast.Term.App(Ast.Term.Const f, tl) ->
       let state, rev_tl =
         List.fold_left (fun (state, tl) t ->
           let state, t = aux true lvl state t in
           (state, t::tl))
          (state, []) tl in
       let tl = List.rev rev_tl in
       let state, c = stack_funct_of_ast inner lvl state f in
       begin match c with
       | Const c -> begin match tl with
          | hd2::tl -> state, Term.App(c,hd2,tl)
          | _ -> anomaly "Application node with no arguments" end
       | App(c,hd1,tl1) -> (* FG:decurrying: is this the right place for it? *)
          state, Term.App(c,hd1,tl1@tl)
       | Builtin(c,tl1) -> state, Term.Builtin(c,tl1@tl)
       | Lam _ -> (* macro with args *)
          state, R.deref_appuv ~from:lvl ~to_:lvl tl c
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
       let state, t' = aux true (lvl+1) state t in
       state, Term.Lam t'
    | Ast.Term.Lam (x,t) ->
       let orig_varmap = get_varmap state in
       let state = update_varmap state (F.Map.add x (mkConst lvl)) in
       let state, t' = aux true (lvl+1) state t in
       set_varmap state orig_varmap, Term.Lam t'
    | Ast.Term.App (Ast.Term.App (f,l1),l2) ->
       aux inner lvl state (Ast.Term.App (f, l1@l2))
    | Ast.Term.CData c -> state, Term.CData (CData.hcons c)
    | Ast.Term.App (Ast.Term.Lam _,_) -> error ~loc "Beta-redexes not in our language"
    | Ast.Term.App (Ast.Term.CData _,_) -> type_error ~loc "Applied literal"
    | Ast.Term.Quoted { Ast.Term.data; kind = None; loc } ->
         let unquote =
           option_get ~err:"No default quotation" !default_quotation in
         let state = set_mtm state (Some { macros = macro}) in
         begin try unquote ~depth:lvl state loc data 
         with Parser.ParseError(loc,msg) -> error ~loc msg end
    | Ast.Term.Quoted { Ast.Term.data; kind = Some name; loc } ->
         let unquote = 
           try StrMap.find name !named_quotations
           with Not_found -> anomaly ("No '"^name^"' quotation") in
         let state = set_mtm state (Some { macros = macro}) in
         begin try unquote ~depth:lvl state loc data
         with Parser.ParseError(loc,msg) -> error ~loc msg end
    | Ast.Term.App (Ast.Term.Quoted _,_) -> type_error ~loc "Applied quotation"
  in

  (* arg_lvl is the number of local variables *)
  aux false arg_lvl state ast
;;

let lp ~depth state loc s =
  let loc, ast = Parser.parse_goal ~loc s in
  let macros =
    match get_mtm state with
    | None -> F.Map.empty
    | Some x -> x.macros in
  preterm_of_ast loc ~depth macros state ast

let prechr_rule_of_ast depth macros state r =
  let pcloc = r.Ast.Chr.loc in
  let state = set_argmap state empty_amap in
  let intern state t = preterm_of_ast pcloc ~depth macros state t in
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
  let state = set_argmap state empty_amap in
  let pname = r.Ast.Chr.attributes.StructuredAST.cid in
  let pifexpr = r.Ast.Chr.attributes.StructuredAST.cifexpr in
  state,
  { pto_match; pto_remove; pguard; pnew_goal; pamap; pname; pifexpr; pcloc }
  
(* exported *)
let preterm_of_function ~depth macros state f =
  let state = set_argmap state empty_amap in
  let state = set_mtm state (Some { macros }) in
  let state, (loc, term) = f state in
  let amap = get_argmap state in
  let state = set_argmap state empty_amap in
  let state = set_mtm state None in
  state, { amap; term; loc }
  
let preterms_of_ast loc ~depth macros state f t =
  let state = set_argmap state empty_amap in
  let state, term = preterm_of_ast loc ~depth macros state t in
  let state, terms = f ~depth state term in
  let amap = get_argmap state in
  let state = set_argmap state empty_amap in
  let state = set_mtm state None in
  (* TODO: may have spurious entries in the amap *)
  state, List.map (fun (loc,term) -> { term; amap; loc }) terms
;;
let preterm_of_ast ~depth macros state (loc, t) =
  let state = set_argmap state empty_amap in
  let state, term = preterm_of_ast loc ~depth macros state t in
  let amap = get_argmap state in
  let state = set_argmap state empty_amap in
  let state = set_mtm state None in
  state, { term; amap; loc }
;;

  open StructuredAST

  let check_no_overlap_macros _ _ = ()
 
  let compile_macro m { Ast.Macro.loc; name = n; body } =
    if F.Map.mem n m then begin
      let _, old_loc = F.Map.find n m in
      error ~loc ("Macro "^F.show n^" declared twice:\n"^
             "first declaration: " ^ Loc.show old_loc ^"\n"^
             "second declaration: " ^ Loc.show loc)
    end;
    F.Map.add n (body,loc) m

  let compile_type lcs macros state { Ast.Type.attributes; loc; name; ty } =
    let tname, _ = C.funct_of_ast name in
    let state, ttype = preterm_of_ast ~depth:lcs macros state (loc, ty) in
    state, { Structured.tindex = attributes; loc; decl = { tname; ttype } }

   let funct_of_ast state c =
     try
       match F.Map.find c (get_varmap state) with
       | Const x -> x 
       | _ -> assert false
     with Not_found -> fst (C.funct_of_ast c)

  let check_duplicate_mode name mode map =
    if C.Map.mem name map && C.Map.find name map <> mode then
      error ("Duplicate mode declaration for " ^ C.show name)

  let compile_mode state modes { Ast.Mode.name; args } =
    let mname = funct_of_ast state name in
    check_duplicate_mode mname args modes;
    C.Map.add mname args modes

  let merge_modes m1 m2 =
    C.Map.fold (fun k v m ->
      check_duplicate_mode k v m;
      C.Map.add k v m)
    m2 m1

  let merge_types t1 t2 = t1 @ t2

  let rec toplevel_clausify loc ~depth state t =
    let state, cl = map_acc (pi2arg loc ~depth []) state (R.split_conj ~depth t) in
    state, List.concat cl
  and pi2arg loc ~depth acc state = function
    | App(c,Lam t,[]) when c == C.pic ->
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

  let compile_shorthand state { StructuredAST.full_name; short_name; iloc } = 
    let full_name = funct_of_ast state full_name in
    let short_name = funct_of_ast state short_name in
  { StructuredAST.full_name; short_name; iloc }

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

  let global_hd_symbols_of_clauses cl =
    List.fold_left (fun s { Ast.Clause.body = { term } } ->
      match term with
      | (Const c | App(c,_,_)) when c != C.rimplc && c < 0 ->
           C.Set.add c s
      | App(ri,(Const c | App(c,_,_)), _) when ri == C.rimplc && c < 0 ->  
           C.Set.add c s
      | (Const _ | App _) -> s
      | Builtin(c,_) -> C.Set.add c s
      | _ -> assert false)
      C.Set.empty cl

  let namespace_separator = "."

  let prefix_const prefix c =
    let c' =
      C.from_stringc (String.concat namespace_separator prefix ^
                      namespace_separator ^
                      C.show c) in
    (* Printf.eprintf "%s -> %s\n" (C.show c) (C.show c'); *)
    c'

  let prepend p s =
    (* XXX OCaml 4.04: C.Set.map (prefix_const [p]) s *)
    let res = ref C.Set.empty in
    C.Set.iter (fun x -> res := C.Set.add (prefix_const [p] x) !res) s;
    !res


  let run ~flags:_ state p =
 (* FIXME: otypes omodes - NO, rewrite spilling on data.term *)
    let rec compile_program omacros lcs state { macros; types; modes; body } =
      check_no_overlap_macros omacros macros;
      let active_macros =
        List.fold_left compile_macro omacros macros in
      let state, types =
        map_acc (compile_type lcs active_macros) state types in
      let modes =
        List.fold_left (compile_mode state) C.Map.empty modes in
      let defs_m = defs_of_modes modes in
      let defs_t = defs_of_types types in
      let lcs, state, types, modes, defs_b, body =
        compile_body active_macros types modes lcs C.Set.empty state body in
      let symbols = C.Set.(union (union defs_m defs_t) defs_b) in
      state, lcs, active_macros,
      { Structured.types; modes; body; symbols }
  
    and compile_body macros types modes lcs defs state = function
      | [] -> lcs, state, types, modes, defs, []
      | Locals (nlist, p) :: rest ->
          let orig_varmap = get_varmap state in
          let lcs, state =
            List.fold_left (fun (lcs,state) name ->
              let rel = mkConst lcs in
              lcs+1, update_varmap state (F.Map.add name rel))
            (lcs,state) nlist in
          let state, lcs, _,
            { Structured.types = tp; modes = mp; body; symbols }
            =
            compile_program macros lcs state p in
          let defs = C.Set.union defs symbols in
          let modes = merge_modes modes mp in
          let types = merge_types types tp in
          let state = set_varmap state orig_varmap in
          let lcs, state, types, modes, defs, compiled_rest =
            compile_body macros types modes lcs defs state rest in
          lcs, state, types, modes, defs, append_body body compiled_rest
      | Clauses cl :: rest ->
          let lcs, state, compiled_cl = compile_clauses lcs state macros cl in
          let compiled_cl = List.concat compiled_cl in
          let defs =
            C.Set.union defs (global_hd_symbols_of_clauses compiled_cl) in
          let compiled_cl = [Structured.Clauses compiled_cl] in
          let lcs, state, types, modes, defs, compiled_rest =
            compile_body macros types modes lcs defs state rest in
          lcs, state, types, modes, defs, append_body compiled_cl compiled_rest
      | Namespace (prefix, p) :: rest ->
          let prefix = F.show prefix in
          let state, lcs, _, p = compile_program macros lcs state p in
          let lcs, state, types, modes, defs, compiled_rest =
            compile_body macros types modes lcs defs state rest in
          lcs, state, types, modes,
          C.Set.union defs (prepend prefix p.Structured.symbols),
          Structured.Namespace(prefix, p) :: compiled_rest
      | Shorten(shorthands,p) :: rest ->
          let shorthands = List.map (compile_shorthand state) shorthands in
          let shorts = List.fold_left (fun s { short_name } ->
            C.Set.add short_name s) C.Set.empty shorthands in
          let state, lcs, _, p = compile_program macros lcs state p in
          let lcs, state, types, modes, defs, compiled_rest =
            compile_body macros types modes lcs defs state rest in
          lcs, state, types, modes,
          C.Set.union defs (C.Set.diff p.Structured.symbols shorts),
          Structured.Shorten(shorthands, p) :: compiled_rest
      | Constraints (clique, rules, p) :: rest ->
          (* XXX missing check for nested constraints *)
          let clique = List.map (funct_of_ast state) clique in
          let state, rules =
            map_acc (prechr_rule_of_ast lcs macros) state rules in
          let state, lcs, _, p = compile_program macros lcs state p in
          let lcs, state, types, modes, defs, compiled_rest =
            compile_body macros types modes lcs defs state rest in
          lcs, state, types, modes,
          C.Set.union defs p.Structured.symbols,
          Structured.Constraints(clique, rules,p) :: compiled_rest
    in
    let state, local_names, toplevel_macros, pbody =
      compile_program F.Map.empty 0 state p in
    state, { Structured.local_names; pbody; toplevel_macros }

end (* }}} *)

let lp = ToDBL.lp
let is_Arg = ToDBL.is_Arg
let fresh_Arg = ToDBL.fresh_Arg
let mk_Arg = ToDBL.mk_Arg
let get_Args = ToDBL.get_Args
let get_Arg = ToDBL.get_Arg


module Flatten : sig

  (* Eliminating the structure (name spaces) *)

  val run : flags:flags -> State.t -> Structured.program -> Flat.program

end = struct (* {{{ *)


  open Structured
  open Flat

  (* Customs are already translated inside terms,
   * may sill require translation inside type/modes declaration *)

  let smart_map_term f t =
    let rec aux = function
      | Const c as x ->
          let c1 = f c in
          if c == c1 then x else mkConst c1
      | Lam t as x ->
          let t1 = aux t in
          if t == t1 then x else Lam t1
      | AppArg(i,ts) as x ->
          let ts1 = smart_map aux ts in
          if ts == ts1 then x else AppArg(i,ts1)
      | AppUVar(r,lvl,ts) as x ->
          assert(!!r == C.dummy);
          let ts1 = smart_map aux ts in
          if ts == ts1 then x else AppUVar(r,lvl,ts1)
      | Builtin(c,ts) as x ->
          if f c != c then
            error ("declaring a clause for builtin: " ^ Constants.show c);
          let ts1 = smart_map aux ts in
          if ts == ts1 then x else Builtin(c,ts1)
      | App(c,t,ts) as x ->
          let c1 = f c in
          let t1 = aux t in
          let ts1 = smart_map aux ts in
          if c == c1 && t == t1 && ts == ts1 then x else App(c1,t1,ts1)
      | Cons(hd,tl) as x ->
          let hd1 = aux hd in
          let tl1 = aux tl in
          if hd == hd1 && tl == tl1 then x else Cons(hd1,tl1)
      | UVar(r,_,_) as x ->
          assert(!!r == C.dummy);
          x
      | (Arg _ | CData _ | Nil | Discard) as x -> x
    in
      aux t

  let smart_map_type f ({ Structured.loc; tindex; decl = { tname; ttype }} as tdecl) =
    let tname1 = f tname in
    let ttype1 = smart_map_term f ttype.term in
    if tname1 == tname && ttype1 == ttype.term then tdecl
    else { Structured.loc; tindex; decl = { tname = tname1; ttype = { term = ttype1; amap = ttype.amap; loc = ttype.loc } } }


  let map_sequent f { peigen; pcontext; pconclusion } =
    {
      peigen = smart_map_term f peigen;
      pcontext = smart_map_term f pcontext;
      pconclusion =smart_map_term f pconclusion;
    }

  let map_chr f
    { pto_match; pto_remove; pguard; pnew_goal; pamap; pifexpr; pname; pcloc }
  =
    {
      pto_match = smart_map (map_sequent f) pto_match;
      pto_remove = smart_map (map_sequent f) pto_remove;
      pguard = option_map (smart_map_term f) pguard;
      pnew_goal = option_map (map_sequent f) pnew_goal;
      pamap; pifexpr; pname; pcloc;
    }

  let map_clause f ({ Ast.Clause.body = { term; amap; loc } } as x) =
    { x with Ast.Clause.body = { term = smart_map_term f term; amap; loc } }

  type subst = (string list * (C.t -> C.t))

  let apply_subst (f : (C.t -> C.t) -> 'a -> 'a) (s : subst) : 'a -> 'a =
    fun x -> f (snd s) x

  let apply_subst_list f = apply_subst (fun x -> smart_map (f x))

  let apply_subst_constant = apply_subst (fun f x -> f x)

  let apply_subst_types = apply_subst_list smart_map_type

  let apply_subst_modes =
    apply_subst (fun f modes ->
       C.Map.fold (fun c v m -> C.Map.add (f c) v m) modes C.Map.empty)

  let apply_subst_chr = apply_subst_list map_chr

  let apply_subst_clauses = apply_subst_list map_clause
    
  let push_subst extra_prefix symbols_affected (oldprefix, oldsubst) =
    let newprefix = oldprefix @ [extra_prefix] in
    let newsubst c =
      if C.Set.mem c symbols_affected then ToDBL.prefix_const newprefix c
      else oldsubst c in
    (newprefix, newsubst)

  let push_subst_shorthands shorthands _symbols_defined (oldprefix, oldsubst) =
    let push1 subst { StructuredAST.short_name; full_name } c =
      if c == short_name then subst full_name
      else subst c
    in
    oldprefix, List.fold_left push1 oldsubst shorthands

  let rec compile_body lcs types modes clauses chr subst state bl =
    match bl with
    | [] -> types, modes, clauses, chr
    | Shorten(shorthands, { types = t; modes = m; body; symbols }) :: rest ->
        let insubst = push_subst_shorthands shorthands symbols subst in
        let types = ToDBL.merge_types (apply_subst_types insubst t) types in
        let modes = ToDBL.merge_modes (apply_subst_modes insubst m) modes in
        let types, modes, clauses, chr =
          compile_body lcs types modes clauses chr insubst state body in
        compile_body lcs types modes clauses chr subst state rest
    | Namespace (extra, { types = t; modes = m; body; symbols }) :: rest ->
        let insubst = push_subst extra symbols subst in
        let types = ToDBL.merge_types (apply_subst_types insubst t) types in
        let modes = ToDBL.merge_modes (apply_subst_modes insubst m) modes in
        let types, modes, clauses, chr =
          compile_body lcs types modes clauses chr insubst state body in
        compile_body lcs types modes clauses chr subst state rest
    | Clauses cl :: rest ->
        let cl = apply_subst_clauses subst cl in
        let clauses = clauses @ cl in
        compile_body lcs types modes clauses chr subst state rest
    | Constraints (clique, rules, { types = t; modes = m; body }) :: rest ->
        let types = ToDBL.merge_types t types in
        let modes = ToDBL.merge_modes m modes in
        let clique = List.map (apply_subst_constant subst) clique in
        let rules = apply_subst_chr subst rules in
        let chr = (clique, rules) :: chr in
        let types, modes, clauses, chr =
          compile_body lcs types modes clauses chr subst state body in
        compile_body lcs types modes clauses chr subst state rest

  let run ~flags:_ state
    { Structured.local_names;
      pbody = { types; modes; body; symbols = _ };
      toplevel_macros;
    }
  =
    let types, modes, clauses, chr =
      compile_body local_names types modes [] [] ([],fun x -> x) state body in
    { Flat.types;
      modes;
      clauses;
      chr = List.rev chr;
      local_names;
      toplevel_macros;
    }

end (* }}} *)

module Spill : sig

  (* Eliminate {func call} *)

  val run : flags:flags -> Flat.program -> Flat.program

  (* Exported to compile the query *)
  val spill_preterm :
    Structured.typ list -> mode C.Map.t -> preterm -> preterm

end = struct (* {{{ *)

  let rec read_ty = function
    | App(c,x,[y]) when c == C.variadic -> `Variadic (read_ty x,read_ty y)
    | App(c,x,[y]) when c == C.arrowc -> 
        let ty_x = read_ty x in
        begin match read_ty y with
        | `Arrow(tys,ty) -> `Arrow (ty_x :: tys, ty)
        | ty -> `Arrow([ty_x], ty) end
    | Const _ as x when x == C.prop -> `Prop
    | _ -> `Unknown

  let type_of_const types c =
    try
      let { Structured.decl = { ttype } } =
        List.find (fun { Structured.decl = { tname } } -> tname == c) types in
      read_ty ttype.term
    with
      Not_found -> `Unknown

  let missing_args_of loc modes types t =
    let c, args =
      let rec aux = function
        | App (c,_,[x]) when c == C.implc -> aux x
        | App (c,x,xs) when c == C.andc || c == C.andc2 ->
            aux List.(hd (rev (x :: xs)))
        | App (c,x,xs) -> c, x :: xs
        | Const c -> c, []
        | Builtin(c,args) -> c, args
        | _ -> error ~loc "Only applications can be spilled" 
      in
        aux t in
    let ty = type_of_const types c in
    let ty_mode, mode =
      match C.Map.find c modes with
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
              (C.show c) output_suffix missing);
          missing
      | _ -> error ~loc ("Cannot spill: unknown arity of " ^ C.show c) in
    if missing_args <= 0 then
      error ~loc ("Cannot spill: " ^ C.show c ^ " is fully applied");
    missing_args

  let spill_term loc modes types argmap term =

    let argmap = ref argmap in
    let mk_Arg n =
      let m, (x,_) = Data.mk_Arg n !argmap in
      argmap := m;
      x in

    let mkAppC c = function
      | [] -> mkConst c
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
        | App(c,x,[y]) when c == C.implc ->
            mkAppC c [x;aux y]
        | App (c,x,xs) when c == C.andc || c == C.andc2 ->
            mkAppC c (on_last aux (x::xs))
        | t -> mkApp t args
      in
        aux fcall in

    let rec apply_to names variable = function
      | Const f as x when List.exists (equal_term x) names ->
          mkAppC f [variable]
      | (Const _ | CData _ | Nil | Discard) as x -> x
      | Cons(hd,tl) ->
          Cons(apply_to names variable hd,apply_to names variable tl)
      | Lam t -> Lam (apply_to names variable t)
      | App(f,x,xs) when List.exists (equal_term (Const f)) names ->
          mkAppC f (List.map (apply_to names variable) (x::xs) @ [variable])
      | App(hd,x,xs) -> mkAppC hd (List.map (apply_to names variable) (x::xs))
      | Builtin(hd,xs) -> Builtin(hd, List.map (apply_to names variable) xs)
      | (Arg _ | AppArg _ | UVar _ | AppUVar _) -> assert false in

    let add_spilled sp t =
      if sp = [] then t else
      mkAppC C.andc (List.map snd sp @ [t]) in

    let rec spaux (depth,vars as ctx) = function
      | App(c, fcall, rest) when c == C.spillc ->
         assert (rest = []);
         let spills, fcall = spaux1 ctx fcall in
         let args =
            mkSpilled (List.rev vars) (missing_args_of loc modes types fcall) in
         spills @ [args, mkAppSpilled fcall args], args
      | App(c, Lam arg, []) when c == C.pic ->
         let ctx = depth+1, mkConst depth :: vars in
         let spills, arg = spaux1 ctx arg in
         [], [mkAppC c [Lam (add_spilled spills arg)]]
      | App(c, Lam arg, []) when c == C.sigmac ->
         let ctx = depth+1, vars in
         let spills, arg = spaux1 ctx arg in
         [], [mkAppC c [Lam (add_spilled spills arg)]]
      | App(c, hyp, [concl]) when c == C.implc ->
         let spills_hyp, hyp1 = spaux1 ctx hyp in
         let t = spaux1_prop ctx concl in
         if (spills_hyp != []) then
           error ~loc "Cannot spill in the head of a clause";
         [], [mkAppC c (hyp1 :: t)]
      | App(c, concl, [hyp]) when c == C.rimplc ->
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
             | `Arrow(_ :: ty,c), a1 :: an ->
                   spaux ctx a1 @@@ aux (`Arrow(ty,c)) an
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
         let sp, t = spaux1 (depth+1, mkConst depth :: vars) t in
         let (t,_), sp = map_acc (fun (t,n) (names, call) ->
               let all_names = names @ n in
               let call = apply_to all_names (mkConst depth) call in
               let t = apply_to names (mkConst depth) t in
               (t,all_names), (names, mkAppC C.pic [Lam call])
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
    assert(sp = []);
    !argmap, term

  let spill_presequent modes types loc pamap ({ pconclusion } as s) =
    let pamap, pconclusion = spill_term loc modes types pamap pconclusion in
    pamap, { s with pconclusion }

  let spill_rule modes types ({ pguard; pnew_goal; pamap; pcloc } as r) =
    let pamap, pguard = option_mapacc (spill_term pcloc modes types) pamap pguard in
    let pamap, pnew_goal =
      option_mapacc (spill_presequent modes types pcloc) pamap pnew_goal in
    { r with pguard; pnew_goal; pamap }

  let spill_chr modes types (clique, rules) =
    let rules = List.map (spill_rule modes types) rules in
    (clique, rules)

  let spill_clause modes types ({ Ast.Clause.body = { term; amap; loc } } as x) =
    let amap, term = spill_term loc modes types amap term in
    { x with Ast.Clause.body = { term; amap; loc } }

  let run ~flags:_ ({ Flat.clauses; modes; types; chr } as p) =
    let clauses = List.map (spill_clause modes types) clauses in
    let chr = List.map (spill_chr modes types) chr in
    { p with Flat.clauses; chr }

  let spill_preterm types modes { term; amap; loc } =
    let amap, term = spill_term loc modes types amap term in
    { amap; term; loc }

end (* }}} *)

module Assemble : sig

  val run : flags:flags -> Flat.program list -> Assembled.program

end = struct (* {{{ *)

  let sort_insertion l =
    let add s { Ast.Clause.attributes = { Assembled.id }; loc } =
      match id with
      | None -> s
      | Some n ->
          if StrMap.mem n s then
            error ~loc ("a clause named " ^ n ^
                   " already exists at " ^ Loc.show (StrMap.find n s))
          else
            StrMap.add n loc s in
    let compile_clause ({ Ast.Clause.attributes = { StructuredAST.id; ifexpr }} as c) =
      { c with Ast.Clause.attributes = { Assembled.id; ifexpr }}
    in
    let rec insert loc_name c l =
      match l, loc_name with
      | [],_ -> error ~loc:c.Ast.Clause.loc ("unable to graft this clause: no clause named " ^
             match loc_name with
             | StructuredAST.After x -> x
             | StructuredAST.Before x -> x)
      | { Ast.Clause.attributes = { Assembled.id = Some n }} as x :: xs,
        StructuredAST.After name when n = name ->
           c :: x :: xs
      | { Ast.Clause.attributes = { Assembled.id = Some n }} as x :: xs,
        StructuredAST.Before name when n = name ->
           x :: c :: xs
      | x :: xs, _ -> x :: insert loc_name c xs in
    let rec aux seen acc = function
      | [] -> List.rev acc
      | { Ast.Clause.attributes = { StructuredAST.insertion = Some i }} as x :: xs ->
          let x = compile_clause x in
          aux (add seen x) (insert i x acc) xs
      | x :: xs ->
          let x = compile_clause x in
          aux (add seen x) (x :: acc) xs
    in
    aux StrMap.empty  [] l

  let run ~flags:_ pl =
    if List.length pl <> 1 then
      error "Only 1 program assembly is supported";
    let { Flat.clauses; types; modes; chr; local_names; toplevel_macros } =
      List.hd pl in
    let clauses = sort_insertion clauses in
    { Assembled.clauses; types; modes; chr; local_names; toplevel_macros }

end (* }}} *)


(****************************************************************************
  API
 ****************************************************************************)

(* Compiler passes *)
let program_of_ast ~flags:({ print_passes } as flags) p =

  if print_passes then
    Format.eprintf "== AST ================@\n@[<v 0>%a@]@\n"
      Ast.Program.pp p;
 
  let p = RecoverStructure.run ~flags p in
 
  if print_passes then
    Format.eprintf "== StructuredAST ================@\n@[<v 0>%a@]@\n"
      StructuredAST.pp_program p;
 
  let s, p = ToDBL.run ~flags (State.init()) p in
 
  if print_passes then
    Format.eprintf "== Structured ================@\n@[<v 0>%a@]@\n"
      Structured.pp_program p;
 
  let p = Flatten.run ~flags s p in
 
  if print_passes then
    Format.eprintf "== Flat ================@\n@[<v 0>%a@]@\n"
      Flat.pp_program p;
 
  let p = Spill.run ~flags p in
 
  if print_passes then
    Format.eprintf "== Spilled ================@\n@[<v 0>%a@]@\n"
      Flat.pp_program p;
 
  let p = Assemble.run ~flags [ p ] in
 
  if print_passes then
    Format.eprintf "== Assembled ================@\n@[<v 0>%a@]@\n"
      Assembled.pp_program p;
 
  {
    Compiled.assembled_program = p;
    compiler_state = s;
    compiler_flags = flags;
  }
;;

let is_builtin tname =
  let all_builtin = BuiltInPredicate.all () in
  let elpi_builtins = [C.cutc;C.declare_constraintc;C.print_constraintsc] in
  List.memq tname elpi_builtins || List.exists ((==) tname) all_builtin
  
let check_all_builtin_are_typed types =
   List.iter (fun c ->
     if not (List.exists
        (fun { Structured.tindex; loc; decl = { tname }} ->
            tindex = StructuredAST.External && tname == c) types) then
       error ("Built-in without external type declaration: " ^ C.show c))
   (BuiltInPredicate.all ());
  List.iter (fun { Structured.tindex; loc; decl = { tname }} ->
    if tindex = StructuredAST.External && not (is_builtin tname) then
      error ~loc ("external type declaration without Built-in: " ^
            C.show tname))
  types
;;

let check_no_regular_types_for_builtins types =
  List.iter (fun {Structured.tindex; loc; decl = { tname } } ->
    if tindex <> StructuredAST.External && is_builtin tname then
      error ~loc ("type declaration for Built-in " ^
            C.show tname ^ " must be flagged as external");
 ) types

let stack_term_of_preterm ~depth:arg_lvl { term = t; amap = { c2i } } =
  let rec stack_term_of_preterm = function
    | Const c when C.Map.mem c c2i -> 
        let argno = C.Map.find c c2i in
        R.mkAppArg argno arg_lvl []
    | Const c -> mkConst c
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
    | UVar _ | AppUVar _ | Arg _ | AppArg _ -> assert false
    | Nil as x -> x
    | Discard as x -> x
    | Cons(hd, tl) as x ->
        let hd1 = stack_term_of_preterm hd in
        let tl1 = stack_term_of_preterm tl in
        if hd == hd1 && tl == tl1 then x else Cons(hd1,tl1)
  in
  stack_term_of_preterm t
;;

let uvbodies_of_assignments assignments =
   State.end_compilation (StrMap.map (function
     | UVar(b,_,_) | AppUVar(b,_,_) -> b
     | _ -> assert false) assignments)

let query_of_ast { Compiled.assembled_program; compiler_state; compiler_flags } t
=
  let initial_depth = assembled_program.Assembled.local_names in
  let types = assembled_program.Assembled.types in
  let modes = assembled_program.Assembled.modes in
  let active_macros = assembled_program.Assembled.toplevel_macros in
  let state, query =
    ToDBL.preterm_of_ast ~depth:initial_depth active_macros compiler_state t in
  let query = Spill.spill_preterm types modes query in
  let query_env = Array.make query.amap.nargs C.dummy in
  let initial_goal =
    R.move ~adepth:initial_depth ~from:initial_depth ~to_:initial_depth query_env
      (stack_term_of_preterm ~depth:initial_depth query) in
  let assignments = StrMap.map (fun i -> query_env.(i)) query.amap.n2i in
  {
    WithMain.types;
    modes;
    clauses = assembled_program.Assembled.clauses;
    chr = assembled_program.Assembled.chr;
    initial_depth;
    query;
    query_arguments = Query.N;
    initial_goal;
    assignments;
    initial_state = state |> (uvbodies_of_assignments assignments);
    compiler_flags;
  }

let query_of_term { Compiled.assembled_program; compiler_state; compiler_flags } f =
  let initial_depth = assembled_program.Assembled.local_names in
  let types = assembled_program.Assembled.types in
  let modes = assembled_program.Assembled.modes in
  let active_macros = assembled_program.Assembled.toplevel_macros in
  let state, query =
    ToDBL.preterm_of_function
      ~depth:initial_depth active_macros compiler_state
      (f ~depth:initial_depth) in
  let query_env = Array.make query.amap.nargs C.dummy in
  let initial_goal =
    R.move ~adepth:initial_depth ~from:initial_depth ~to_:initial_depth query_env
      (stack_term_of_preterm ~depth:initial_depth query) in
  let assignments = StrMap.map (fun i -> query_env.(i)) query.amap.n2i in
 {
    WithMain.types;
    modes;
    clauses = assembled_program.Assembled.clauses;
    chr = assembled_program.Assembled.chr;
    initial_depth;
    query;
    query_arguments = Query.N;
    initial_goal;
    assignments;
    initial_state = state |> (uvbodies_of_assignments assignments);
    compiler_flags;
  }


let query_of_data p loc (Query.Query { arguments } as descr) =
  let query = query_of_term p (fun ~depth state ->
    let state, term = Query.embed_query ~mk_Arg ~depth state descr in
    state, (loc, term)) in
  { query with query_arguments = arguments }
  
module Compiler : sig

  (* Translates preterms in terms and AST clauses into clauses (with a key,
   * subgoals, etc *)

  val run : 'a query -> 'a executable

end = struct (* {{{ *)

let compile_chr depth
    { pto_match; pto_remove; pguard; pnew_goal; pamap; pname; pcloc = loc }
=
  if depth > 0 then error ~loc "CHR: rules and locals are not supported";
  let key_of_sequent { pconclusion } =
    match pconclusion with
    | Const x -> x
    | App(x,_,_) -> x
    | f -> error ~loc "CHR: rule without head symbol" in
  let stack_term_of_preterm term =
    stack_term_of_preterm ~depth:0 { term; amap = pamap; loc } in
  let stack_sequent_of_presequent { pcontext; pconclusion; peigen } =
    let context = stack_term_of_preterm pcontext in
    let conclusion = stack_term_of_preterm pconclusion in
    let eigen = stack_term_of_preterm peigen in
    { CHR.context; conclusion; eigen } in
  let all_sequents = pto_match @ pto_remove in
  let pattern = List.map key_of_sequent all_sequents in
  { CHR.to_match = List.map stack_sequent_of_presequent pto_match;
        to_remove = List.map stack_sequent_of_presequent pto_remove;
        patsno = List.(length pto_match + length pto_remove);
        guard = option_map stack_term_of_preterm pguard;
        new_goal = option_map stack_sequent_of_presequent pnew_goal;
        nargs = pamap.nargs;
        pattern;
        rule_name = pname;
      }
;;
  
let compile_clause modes initial_depth
    { Ast.Clause.body = ({ amap = { nargs }} as body); loc }
=
  let body = stack_term_of_preterm ~depth:0 body in
  let cl, _, morelcs = R.clausify1 ~loc modes ~nargs ~depth:initial_depth body in
  if morelcs <> 0 then error ~loc "sigma in a toplevel clause is not supported";
  cl

let rec filter_if defs proj = function
  | [] -> []
  | c :: rest ->
    match proj c with
    | None -> c :: filter_if defs proj rest 
    | Some e when StrSet.mem e defs -> c :: filter_if defs proj rest
    | Some _ -> filter_if defs proj rest


let chose_indexing predicate l =
  let rec all_zero = function
    | [] -> true
    | 0 :: l -> all_zero l
    | _ -> false in
  let rec aux n = function
    | [] -> error ("Wrong indexing for " ^ C.show predicate)
    | 0 :: l -> aux (n+1) l
    | 1 :: l when all_zero l -> MapOn n
    | _ -> Hash l
  in
    aux 0 l

let run
  {
    WithMain.types;
    modes;
    clauses;
    chr;
    initial_depth;
    initial_goal;
    assignments;
    initial_state;
    compiler_flags = flags;
    query_arguments;
  }
=

  if not flags.allow_untyped_builtin then
    check_all_builtin_are_typed types;
  check_no_regular_types_for_builtins types;
  (* Real Arg nodes: from "Const '%Arg3'" to "Arg 3" *)
  let pifexpr { pifexpr } = pifexpr in
  let chr =
    List.fold_left (fun chr (clique, rules) ->
      let chr, clique = CHR.new_clique clique chr in
      let rules = filter_if flags.defined_variables pifexpr rules in 
      let rules = List.map (compile_chr initial_depth) rules in
      List.fold_left (fun x y -> CHR.add_rule clique y x) chr rules)
    CHR.empty chr in
  let ifexpr { Ast.Clause.attributes = { Assembled.ifexpr } } = ifexpr in
  let indexing =
    let known =
      let ty = List.map (fun { Structured.decl = { tname }} -> tname) types in
      let mo = C.Map.bindings modes |> List.map fst in
      List.fold_right C.Set.add (mo @ ty) C.Set.empty in
    C.Set.fold (fun name m ->
      let mode = try C.Map.find name modes with Not_found -> [] in
      let index =
        let indexes =
          map_filter (fun { Structured.decl = { tname }; tindex } ->
              match tindex with
              | Indexed l when tname == name -> Some l
              | _ -> None) types |> uniq in
        match indexes with
        | [] -> [1]
        | [x] -> x
        | _ -> error ("multiple and inconsistent indexing attributes for " ^
                      C.show name) in
      C.Map.add name (mode,chose_indexing name index) m) known C.Map.empty in
  let prolog_program =
    R.make_index ~depth:initial_depth ~indexing
      (List.map (compile_clause modes initial_depth)
        (filter_if flags.defined_variables ifexpr clauses)) in
  {
    Data.compiled_program = prolog_program;
    chr;
    initial_depth;
    initial_goal;
    initial_state;
    assignments;
    query_arguments;
  }

end (* }}} *)

let executable_of_query = Compiler.run

let term_of_ast ~depth t =
 let argsdepth = depth in
 let state = State.init () in
(*
 let freevars = C.mkinterval 0 depth 0 in
 let state = update_varmap state (fun cmap ->
    List.fold_left (fun cmap i ->
     F.Map.add (F.from_string (C.show (destConst i))) i cmap
     ) F.Map.empty freevars) in
*)
 let _, pt = ToDBL.preterm_of_ast ~depth F.Map.empty state t in
 let t = stack_term_of_preterm ~depth pt in
 let env = Array.make pt.amap.nargs C.dummy in
 R.move ~adepth:argsdepth ~from:depth ~to_:depth env t
;;

let pp_query pp fmt {
    WithMain.types;
    modes;
    clauses;
    chr;
    initial_depth;
    query; } =
  Format.fprintf fmt "@[<v>";
  List.iter (fun { Ast.Clause.body } ->
    Format.fprintf fmt "%a.@;" (pp ~depth:initial_depth)
      (stack_term_of_preterm ~depth:initial_depth body))
  clauses;
  Format.fprintf fmt "?- %a.@;" (pp ~depth:initial_depth)
    (stack_term_of_preterm ~depth:initial_depth query);
  Format.fprintf fmt "@]"
;;

(****************************************************************************
  Quotation (for static checkers, see elpi-quoted_syntax.elpi)
 ****************************************************************************)

let constc = C.from_stringc "const"
let tconstc = C.from_stringc "tconst"
let appc = C.from_stringc "app"
let tappc = C.from_stringc "tapp"
let lamc = C.from_stringc "lam"
let cdatac = C.from_stringc "cdata"
let forallc = C.from_stringc "forall"
let arrowc = C.from_stringc "arrow"
let argc = C.from_stringc "arg"
let discardc = C.from_stringc "discard"
let clausec = C.from_stringc "clause"

let mkQApp ~on_type l =
  let c = if on_type then tappc else appc in
  App(c,R.list_to_lp_list l,[])

let mkQCon ~on_type ?(amap=empty_amap) c =
  try mkConst (C.Map.find c amap.c2i)
  with Not_found ->
    let a = if on_type then tconstc else constc in
    if c < 0 then App(a,Data.C.of_string (C.show c),[])
    else mkConst (c + amap.nargs)

let quote_preterm ?(on_type=false) { term; amap } =
  let mkQApp = mkQApp ~on_type in
  let mkQCon = mkQCon ~on_type ~amap in
  let rec aux depth term = match term with
    | Const n when on_type && C.show n = "string" -> 
        App(C.ctypec, Data.C.of_string "string",[])
    | Const n when on_type && C.show n = "int" ->
        App(C.ctypec, Data.C.of_string "int",[])
    | Const n when on_type && C.show n = "float" ->
        App(C.ctypec, Data.C.of_string "float",[])
    | App(c,CData s,[])
      when on_type && c == C.ctypec && Data.C.is_string s -> term
    | App(c,s,[t]) when on_type && c == C.arrowc ->
        App(arrowc,aux depth s,[aux depth t])
    | Const n when on_type && C.show n = "prop" -> term

    | Const n -> mkQCon n
    | Builtin(c,[]) -> mkQCon c
    | Lam x -> App(lamc,Lam (aux (depth+1) x),[])
    | App(c,x,xs) ->
        mkQApp (mkQCon c :: List.(map (aux depth) (x :: xs)))
    | Builtin(c,args) -> mkQApp (mkQCon c :: List.map (aux depth) args)

(*
    | Arg(id,0) -> mkConst id
    | Arg(id,argno) -> mkQApp (mkConst id :: C.mkinterval vars argno 0)
    | AppArg(id,xs) -> mkQApp (mkConst id :: List.map (aux depth) xs)
*)
    | Arg _ | AppArg _ -> assert false

(*
    | UVar ({ contents = g }, from, args) when g != C.dummy ->
       aux depth (deref_uv ~from ~to_:depth args g)
    | AppUVar ({contents = t}, from, args) when t != C.dummy ->
       aux depth (deref_appuv ~from ~to_:depth args t)
*)
    | UVar _ | AppUVar _ -> assert false

    | CData _ as x -> App(cdatac,x,[])
    | Cons(hd,tl) -> mkQApp [mkQCon C.consc; aux depth hd; aux depth tl]
    | Nil -> mkQCon C.nilc
    | Discard -> mkQCon discardc
  in
    aux amap.nargs term

(* FIXME : close_with_pis already exists but unused *)
let close_w_binder binder t { nargs } =
  let rec close = function
    | 0 -> t
    | n -> App(binder,Lam (close (n-1)),[]) in
  close nargs

let sorted_names_of_argmap argmap =
    IntMap.bindings argmap.i2n |>
    List.map snd |>
    List.map Data.C.of_string

let quote_loc ?id loc =
  let source_name =
    match id with
    | Some x -> loc.Loc.source_name ^ x ^ ":"
    | None -> loc.Loc.source_name in
  Ast.cloc.CData.cin { loc with Loc.source_name }

let quote_clause { Ast.Clause.loc; attributes = { Assembled.id }; body } =
  let clloc = quote_loc ?id loc in
  let qt = close_w_binder argc (quote_preterm body) body.amap in
  let names = sorted_names_of_argmap body.amap in
  App(clausec,CData clloc,[R.list_to_lp_list names; qt])
;;

let quote_syntax { WithMain.clauses; query } =
  let names = sorted_names_of_argmap query.amap in
  let clist = List.map quote_clause clauses in
  let q =
    App(clausec,CData (quote_loc ~id:"query" query.loc),
      [R.list_to_lp_list names;
       close_w_binder argc (quote_preterm ~on_type:false query) query.amap]) in
  clist, q

let default_checker () =
  try Parser.parse_program
         ~print_accumulated_files:false ["elpi-checker.elpi"]
  with Parser.ParseError(loc,err) -> error ~loc err

let static_check header
  ?(exec=R.execute_once ~delay_outside_fragment:false) ?(checker=default_checker ()) ?(flags=default_flags)
  ({ WithMain.types } as q)
=
  let p,q = quote_syntax q in
  let tlist = R.list_to_lp_list (List.map
    (fun { Structured.decl = { tname; ttype } } ->
      App(C.from_stringc "`:",mkQCon ~on_type:false tname,
        [close_w_binder forallc (quote_preterm ~on_type:true ttype)
          ttype.amap]))
    types) in
  let checker =
    program_of_ast
      ~flags:{ flags with allow_untyped_builtin = true }
      (header @ checker) in
  let loc = Loc.initial "(static_check)" in
  let query =
    query_of_term checker (fun ~depth state ->
      assert(depth=0);
      state, (loc,App(C.from_stringc "check",R.list_to_lp_list p,[q;tlist]))) in
  let executable = executable_of_query query in
  exec executable <> Failure
;;

(* vim: set foldmethod=marker: *)
