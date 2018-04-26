(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_data
open Elpi_runtime_trace_off.Elpi_runtime
open Pp

module C = Constants
module CS = CompilerState
module A = Elpi_ast

type flags = {
  defined_variables : StrSet.t;
  allow_untyped_builtin : bool;
}
let default_flags = {
  defined_variables = StrSet.empty;
  allow_untyped_builtin = false;
}

(****************************************************************************
  Intermediate data structures
 ****************************************************************************)

module StructuredAST = struct

type program = {
  macros : (A.Func.t, A.term) A.macro list;   
  types : A.tdecl list;
  modes : A.Func.t A.mode list;
  body : block list
}
and block =
  | Locals of A.Func.t list * program
  | Clauses of (A.term,attribute) A.clause list
  | Namespace of A.Func.t * program
  | Constraints of A.Func.t list * A.chr_rule list * program
and attribute = {
  insertion : insertion option;
  id : string option;
  ifexpr : string option;
}
and insertion = Before of string | After of string
[@@deriving show]

end

module StructuredProgram = struct

type program = { 
  pbody : pbody;      
  local_names : int;
  toplevel_macros : macro_declaration;
}
and pbody = {
  types : (bool * type_declaration) list; (* bool = extern *)
  modes : mode C.Map.t;
  body : block list;
  (* defined (global) symbols (including in sub blocks) *)
  symbols : C.Set.t;
}
and block =
  | Clauses of (preterm,StructuredAST.attribute) A.clause list
  | Namespace of string * pbody
  | Constraints of constant list * prechr_rule list * pbody
[@@deriving show]

end

module Flat = struct

type program = {
  types : (bool * type_declaration) list; 
  modes : mode C.Map.t;
  clauses : (preterm,StructuredAST.attribute) A.clause list;
  chr : (constant list * prechr_rule list) list;
  local_names : int;

  toplevel_macros : macro_declaration;
}
[@@deriving show]

end

module Assembled = struct

type program = {
  types : (bool * type_declaration) list; 
  modes : mode C.Map.t;
  clauses : (preterm,attribute) A.clause list;
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

module Program = struct

(* The entire program + stuff needed in order to run the query *)
type program = {
  assembled_program : Assembled.program;
  compiler_state : CompilerState.t;
}
[@@deriving show]
  
end
type program = Program.program

module Query = struct

(* The entire program + query, but still in "printable" format *)
type query = {
  types : (bool * type_declaration) list; 
  modes : mode C.Map.t;
  clauses : (preterm,Assembled.attribute) A.clause list;
  chr : (constant list * prechr_rule list) list;
  initial_depth : int;
  query : preterm;
  query_loc : Ploc.t;
  initial_constraints : CustomConstraint.t;
}
[@@deriving show]

end
type query = Query.query

module Executable = struct

(* All that is needed in order to execute, and nothing more *)
type executable = Elpi_data.executable = {
  (* the lambda-Prolog program: an indexed list of clauses *) 
  compiled_program : prolog_prog [@printer (pp_extensible pp_prolog_prog)];
  (* Execution modes (needed for hypothetical clauses *)
  modes : mode C.Map.t;
  (* chr rules *)
  chr : CHR.t;
  (* initial depth (used for both local variables and CHR (#eigenvars) *)
  initial_depth : int;
  (* Heap for the query *)
  query_env : env;
  (* query *)
  initial_goal: term;
  (* constraints coming from compilation *)
  initial_constraints : CustomConstraint.t;
  (* solution *)
  assignments_names : int StrMap.t;
}

end

(****************************************************************************
  Compiler
 ****************************************************************************)

module Preprocessing : sig

  (* Reconstructs the structure of the AST (i.e. matches { with }) *)

  val run : A.program -> StructuredAST.program

end = struct (* {{{ *)
  
  open StructuredAST
 
  let cl2b = function
    | [] -> []
    | clauses -> [Clauses (List.rev clauses)]

  let structure_attributes ({ A.attributes; A.loc } as c) =
    let duplicate_err s =
      error (Ploc.show loc ^ ": duplicate attribute " ^ s) in
    let rec aux r = function
      | [] -> r
      | A.Name s :: rest ->
         if r.id <> None then duplicate_err "name";
         aux { r with id = Some s } rest
      | A.After s :: rest ->
         if r.insertion <> None then duplicate_err "insertion";
         aux { r with insertion = Some (After s) } rest
      | A.Before s :: rest ->
         if r.insertion <> None then duplicate_err "insertion";
         aux { r with insertion = Some (Before s) } rest
      | A.If s :: rest ->
         if r.ifexpr <> None then duplicate_err "if";
         aux { r with ifexpr = Some s } rest
    in
    { c with attributes =
        aux { insertion = None; id = None; ifexpr = None } attributes }

  let run dl =
    let rec aux blocks clauses macros types modes  locals chr = function
      | (A.End _ :: _ | []) as rest ->
          { body = List.rev (cl2b clauses @ blocks);
            types = List.rev types;
            macros = List.rev macros;
            modes = List.rev modes },
          locals,
          List.rev chr,
          rest
      | A.Begin loc :: rest ->
          let p, locals1, chr1, rest = aux [] [] [] [] [] [] [] rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside an anonymous block";
          aux_end_block loc (Locals(locals1,p) :: cl2b clauses @ blocks)
            [] macros types modes locals chr rest
      | A.Constraint (loc, f) :: rest ->
          if chr <> [] then
            error "Constraint blocks cannot be nested";
          let p, locals1, chr, rest = aux [] [] [] [] [] [] [] rest in
          if locals1 <> [] then
            error "locals cannot be declared inside a Constraint block";
          aux_end_block loc (Constraints(f,chr,p) :: cl2b clauses @ blocks)
            [] macros types modes locals [] rest
      | A.Namespace (loc, n) :: rest ->
          let p, locals1, chr1, rest = aux [] [] [] [] [] [] [] rest in
          if chr1 <> [] then
            error "CHR cannot be declared inside a namespace block";
          if locals1 <> [] then
            error "locals cannot be declared inside a namespace block";
          aux_end_block loc (Namespace (n,p) :: cl2b clauses @ blocks)
            [] macros types modes locals chr rest

      | A.Accumulated a :: rest ->
          aux blocks clauses macros types modes locals chr (a @ rest)

      | A.Clause c :: rest ->
          let c = structure_attributes c in
          aux blocks (c::clauses) macros types modes locals chr rest
      | A.Macro m :: rest ->
          aux blocks clauses (m::macros) types modes locals chr rest
      | A.Type t :: rest ->
          aux blocks clauses macros (t::types) modes locals chr rest
      | A.Mode ms :: rest ->
          aux blocks clauses macros types (ms @ modes) locals chr rest
      | A.Local l :: rest ->
          aux blocks clauses macros types modes (l::locals) chr rest
      | A.Chr r :: rest ->
          aux blocks clauses macros types modes locals (r::chr) rest

    and aux_end_block loc blocks clauses macros types modes locals chr rest =
      match rest with
      | A.End _ :: rest -> aux blocks clauses macros types modes locals chr rest
      | _ -> error (Ploc.show loc ^ ": matching } is missing")

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

  type quotation = depth:int -> CS.t -> string -> CS.t * term
  let named_quotations = ref StrMap.empty
  let default_quotation = ref None
  
  let set_default_quotation f = default_quotation := Some f
  let register_named_quotation ~name:n f =
    named_quotations := StrMap.add n f !named_quotations

end

include Quotation

module ToDBL : sig
  open C

  (* Eliminates:
     - Locals: become the initial set of pi-quantified vars (local_names)
     - @macros
     - {{quatations}} (may add to the compiler state, later to be turned into
                       initial_constraints)

     Translates AST to preterm (terms where Arg(2) is represented with
     Const "%Arg2")
  *)

  val run : CS.t -> StructuredAST.program -> CS.t * StructuredProgram.program

  (* Exported since also used to flatten (here we "flatten" locals) *)
  val prefix_const : string list -> C.t -> C.t
  val merge_modes : mode Map.t -> mode Map.t -> mode Map.t
  val merge_types :
          (bool * type_declaration) list ->
          (bool * type_declaration) list ->
          (bool * type_declaration) list

  (* Exported to compile the query *)
  val preterm_of_ast :
    depth:int -> macro_declaration -> CompilerState.t ->
      A.term -> CompilerState.t * preterm
  val preterm_of_function :
    depth:int -> macro_declaration -> CompilerState.t -> 
    (CompilerState.t -> CompilerState.t * term) ->
      CompilerState.t * preterm

  (* Exported for quations *)    
  val lp : quotation
  val is_Arg : CompilerState.t -> term -> bool
  val fresh_Arg : 
    CompilerState.t -> name_hint:string -> args:term list ->
      CompilerState.t * string * term

end = struct (* {{{ *)


(* **** ast->term compiler state ***************************************** *) 

let get_argmap, set_argmap, update_argmap =
  let argmap =
    CS.declare ~name:"elpi:argmap" ~pp:todopp
      ~init:(fun () -> empty_amap) in
  CS.(get argmap, set argmap, update_return argmap)

(* For bound variables *)
type varmap = term F.Map.t 

let get_varmap, set_varmap, update_varmap =
  let varmap =
    CS.declare ~name:"elpi:varmap" ~pp:todopp
      ~init:(fun () -> F.Map.empty) in
  CS.(get varmap, set varmap, update varmap)

(* Embed in the state everything, to cross quotations *)

type mtm = {
  macros : macro_declaration;
}

let get_mtm, set_mtm =
  let mtm =
    CS.declare ~name:"elpi:mtm" ~pp:todopp
      ~init:(fun () -> None) in
  CS.(get mtm, set mtm)

(**** utils ******************)

let is_Arg state x =
  let { c2i } = get_argmap state in
  match x with
  | Const c -> C.Map.mem c c2i
  | App(c,_,_) -> C.Map.mem c c2i
  | _ -> false

let mk_Arg state n = update_argmap state (mk_Arg n)

let fresh_Arg =
  let qargno = ref 0 in
  fun state ~name_hint:name ~args ->
    incr qargno;
    let name = Printf.sprintf "%s_%d_" name !qargno in
    let state, (t, c) = mk_Arg state name in
    match args with
    | [] -> state, name, t
    | x::xs -> state, name, App(c,x,xs)

let preterm_of_ast ~depth:arg_lvl macro state ast =

  let is_uvar_name f = 
     let c = (F.show f).[0] in
     ('A' <= c && c <= 'Z') in
    
  let is_discard f =
     let c = (F.show f).[0] in
     c = '_' in

  let is_macro_name f = 
     let c = (F.show f).[0] in
     c = '@' in

  let stack_arg_of_ast state n =
    let { n2t } = get_argmap state in
    try state, StrMap.find n n2t
    with Not_found -> let state, (t, _) = mk_Arg state n in state, t in

  let rec stack_macro_of_ast inner lvl state f =
    try aux inner lvl state (fst (F.Map.find f macro))
    with Not_found -> error ("Undeclared macro " ^ F.show f) 

  (* compilation of "functors" *) 
  and stack_funct_of_ast inner curlvl state f =
    try state, F.Map.find f (get_varmap state)
    with Not_found ->
     if is_discard f then
       state, Discard
     else if is_uvar_name f then
       stack_arg_of_ast state (F.show f)
     else if is_macro_name f then
       stack_macro_of_ast inner curlvl state f
     else if Builtin.is_declared (fst (C.funct_of_ast f)) then
       state, Builtin(fst (C.funct_of_ast f),[])
     else if CustomFunctorCompilation.is_backtick f then
       CustomFunctorCompilation.compile_backtick state f
     else if CustomFunctorCompilation.is_singlequote f then
       CustomFunctorCompilation.compile_singlequote state f
     else state, snd (C.funct_of_ast f)
  
  and aux inner lvl state = function
    | A.Const f when F.(equal f nilf) -> state, Nil
    | A.Const f -> stack_funct_of_ast inner lvl state f
    | A.App(A.Const f, [hd;tl]) when F.(equal f consf) ->
       let state, hd = aux true lvl state hd in
       let state, tl = aux true lvl state tl in
       state, Cons(hd,tl)
    | A.App(A.Const f, tl) ->
       let state, rev_tl =
         List.fold_left (fun (state, tl) t ->
           let state, t = aux true lvl state t in
           (state, t::tl))
          (state, []) tl in
       let tl = List.rev rev_tl in
       let state, c = stack_funct_of_ast inner lvl state f in
       begin match c with
       | Const c -> begin match tl with
          | hd2::tl -> state, App(c,hd2,tl)
          | _ -> anomaly "Application node with no arguments" end
       | App(c,hd1,tl1) -> (* FG:decurrying: is this the right place for it? *)
          state, App(c,hd1,tl1@tl)
       | Builtin(c,tl1) -> state, Builtin(c,tl1@tl)
       | Lam _ -> (* macro with args *)
          state, deref_appuv ~from:lvl ~to_:lvl tl c
       | Discard -> 
          error "Clause shape unsupported: _ cannot be applied"
       | _ -> error "Clause shape unsupported" end
(*
    | A.App (A.Builtin f,tl) ->
       let cname = stack_custom_of_ast f in
       let state, rev_tl =
         List.fold_left (fun (state, tl) t ->
            let state, t = aux true lvl state t in
            (state, t::tl))
          (state, []) tl in
       state, Builtin(cname, List.rev rev_tl)
*)
    | A.Lam (x,t) when A.Func.(equal x dummyname)->
       let state, t' = aux true (lvl+1) state t in
       state, Lam t'
    | A.Lam (x,t) ->
       let orig_varmap = get_varmap state in
       let state = update_varmap state (F.Map.add x (mkConst lvl)) in
       let state, t' = aux true (lvl+1) state t in
       set_varmap state orig_varmap, Lam t'
    | A.App (A.App (f,l1),l2) ->
       aux inner lvl state (A.App (f, l1@l2))
    | A.CData c -> state, CData (CData.hcons c)
    | A.App (A.Lam _,_) -> error "Beta-redexes not in our language"
    | A.App (A.CData _,_) -> type_error "Applied literal"
    | A.Quoted { A.data; A.kind = None } ->
         let unquote =
           option_get ~err:"No default quotation" !default_quotation in
         let state = set_mtm state (Some { macros = macro}) in
         unquote ~depth:lvl state data 
    | A.Quoted { A.data; A.kind = Some name } ->
         let unquote = 
           try StrMap.find name !named_quotations
           with Not_found -> anomaly ("No '"^name^"' quotation") in
         let state = set_mtm state (Some { macros = macro}) in
         unquote ~depth:lvl state data 
    | A.App (A.Quoted _,_) -> type_error "Applied quotation"
  in

  (* arg_lvl is the number of local variables *)
  aux false arg_lvl state ast
;;

let lp ~depth state s =
  let _loc, ast = Elpi_parser.parse_goal_from_stream (Stream.of_string s) in
  let macros =
    match get_mtm state with
    | None -> A.Func.Map.empty
    | Some x -> x.macros in
  preterm_of_ast ~depth macros state ast

let prechr_rule_of_ast depth macros state r =
  let state = set_argmap state empty_amap in
  let intern state t = preterm_of_ast ~depth macros state t in
  let intern_sequent state { A.eigen; context; conclusion } =
    let state, peigen = intern state eigen in
    let state, pcontext = intern state context in
    let state, pconclusion = intern state conclusion in
    state, { peigen; pcontext; pconclusion } in
  let state, pto_match = map_acc intern_sequent state r.A.to_match in
  let state, pto_remove = map_acc intern_sequent state r.A.to_remove in
  let state, pguard = option_mapacc intern state r.A.guard in
  let state, pnew_goal = option_mapacc intern_sequent state r.A.new_goal in
  let pamap = get_argmap state in
  let state = set_argmap state empty_amap in
  state, { pto_match; pto_remove; pguard; pnew_goal; pamap }
  
(* exported *)
let preterm_of_function ~depth macros state f =
  let state = set_argmap state empty_amap in
  let state = set_mtm state (Some { macros }) in
  let state, term = f state in
  let amap = get_argmap state in
  let state = set_argmap state empty_amap in
  let state = set_mtm state None in
  state, { amap; term }
  
let preterms_of_ast ~depth macros state f t =
  let state = set_argmap state empty_amap in
  let state, term = preterm_of_ast ~depth macros state t in
  let state, terms = f ~depth state term in
  let amap = get_argmap state in
  let state = set_argmap state empty_amap in
  let state = set_mtm state None in
  (* TODO: may have spurious entries in the amap *)
  state, List.map (fun term -> { term; amap }) terms
;;
let preterm_of_ast ~depth macros state t =
  let state = set_argmap state empty_amap in
  let state, term = preterm_of_ast ~depth macros state t in
  let amap = get_argmap state in
  let state = set_argmap state empty_amap in
  let state = set_mtm state None in
  state, { term; amap }
;;

  open StructuredAST

  let check_no_overlap_macros _ _ = ()
 
  let compile_macro m { A.mlocation = loc; A.maname = n; A.mbody } =
    if A.Func.Map.mem n m then begin
      let _, old_loc = F.Map.find n m in
      error ("Macro "^Elpi_ast.Func.show n^" declared twice:\n"^
             "first declaration: " ^ Ploc.show old_loc ^"\n"^
             "second declaration: " ^ Ploc.show loc)
    end;
    A.Func.Map.add n (mbody,loc) m

  let compile_type lcs macros state
    { A.textern = is_external; A.tname = name; A.tty = typ }
  =
    let tname, _ = C.funct_of_ast name in
    let state, ttype = preterm_of_ast ~depth:lcs macros state typ in
    state, (is_external, { tname; ttype })

   let funct_of_ast state c =
     try
       match F.Map.find c (get_varmap state) with
       | Const x -> x 
       | _ -> assert false
     with Not_found -> fst (C.funct_of_ast c)

  let check_duplicate_mode name mode map =
    if C.Map.mem name map && C.Map.find name map <> mode then
      error ("Duplicate mode declaration for " ^ C.show name)

  let compile_mode state modes { A.mname; A.margs } =
    let mname = funct_of_ast state mname in
    check_duplicate_mode mname margs modes;
    C.Map.add mname margs modes

  let merge_modes m1 m2 =
    C.Map.fold (fun k v m ->
      check_duplicate_mode k v m;
      C.Map.add k v m)
    m2 m1

  let merge_types t1 t2 = t1 @ t2

  let rec toplevel_clausify ~depth state t =
    let state, cl = map_acc (pi2arg ~depth []) state (split_conj ~depth t) in
    state, List.concat cl
  and pi2arg ~depth acc state = function
    | App(c,Lam t,[]) when c == C.pic ->
        let state, _, arg = fresh_Arg state ~name_hint:"X" ~args:[] in
        pi2arg ~depth (acc @ [arg]) state t
    | t ->
        if acc = [] then state, [t]
        else toplevel_clausify state ~depth (subst ~depth acc t)

  let rec compile_clauses lcs state macros = function
    | [] -> lcs, state, []
    | { A.body; attributes; loc } :: rest ->
      let state, ts =
        preterms_of_ast ~depth:lcs macros state toplevel_clausify body in
      let cl = List.map (fun body -> { A.loc; attributes; body}) ts in
      let lcs, state, rest = compile_clauses lcs state macros rest in
      lcs, state, cl :: rest

  let rec append_body b1 b2 =
    match b1, b2 with
    | [], _ -> b2
    | [StructuredProgram.Clauses c1], StructuredProgram.Clauses c2 :: more ->
         StructuredProgram.Clauses (c1 @ c2) :: more
    | x :: xs, _ -> x :: append_body xs b2

  let defs_of_modes modes =
    C.Map.fold (fun k _ -> C.Set.add k) modes C.Set.empty
  
  let defs_of_types types =
    List.fold_left (fun s (_,{ tname }) -> C.Set.add tname s) C.Set.empty types

  let global_hd_symbols_of_clauses cl =
    List.fold_left (fun s { A.body = { term } } ->
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

  let prepend p s = C.Set.map (prefix_const [p]) s

  let run state p =
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
      { StructuredProgram.types; modes; body; symbols }
  
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
            { StructuredProgram.types = tp; modes = mp; body; symbols }
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
          let compiled_cl = [StructuredProgram.Clauses compiled_cl] in
          let lcs, state, types, modes, defs, compiled_rest =
            compile_body macros types modes lcs defs state rest in
          lcs, state, types, modes, defs, append_body compiled_cl compiled_rest
      | Namespace (prefix, p) :: rest ->
          let prefix = A.Func.show prefix in
          let state, lcs, _, p = compile_program macros lcs state p in
          let lcs, state, types, modes, defs, compiled_rest =
            compile_body macros types modes lcs defs state rest in
          lcs, state, types, modes,C.Set.union defs (prepend prefix p.symbols),
          StructuredProgram.Namespace(prefix, p) :: compiled_rest
      | Constraints (clique, rules, p) :: rest ->
          (* XXX missing check for nested constraints *)
          let clique = List.map (funct_of_ast state) clique in
          let state, rules =
            map_acc (prechr_rule_of_ast lcs macros) state rules in
          let state, lcs, _, p = compile_program macros lcs state p in
          let lcs, state, types, modes, defs, compiled_rest =
            compile_body macros types modes lcs defs state rest in
          lcs, state, types, modes, C.Set.union defs p.symbols,
          StructuredProgram.Constraints(clique, rules,p) :: compiled_rest
    in
    let state, local_names, toplevel_macros, pbody =
      compile_program A.Func.Map.empty 0 state p in
    state, { StructuredProgram.local_names; pbody; toplevel_macros }

end (* }}} *)

let lp = ToDBL.lp
let is_Arg = ToDBL.is_Arg
let fresh_Arg = ToDBL.fresh_Arg

module Flatten : sig

  (* Eliminating the structure (name spaces) *)

  val run : CS.t -> StructuredProgram.program -> Flat.program

end = struct (* {{{ *)


  open StructuredProgram
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
          assert(f c == c);
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

  let smart_map_type f (b, { tname; ttype } as tdecl) =
    let tname1 = f tname in
    let ttype1 = smart_map_term f ttype.term in
    if tname1 == tname && ttype1 == ttype.term then tdecl
    else b, { tname = tname1; ttype = { term = ttype1; amap = ttype.amap } }


  let map_sequent f { peigen; pcontext; pconclusion } =
    {
      peigen = smart_map_term f peigen;
      pcontext = smart_map_term f pcontext;
      pconclusion =smart_map_term f pconclusion;
    }

  let map_chr f
    { pto_match; pto_remove; pguard; pnew_goal; pamap }
  =
    {
      pto_match = smart_map (map_sequent f) pto_match;
      pto_remove = smart_map (map_sequent f) pto_remove;
      pguard = option_map (smart_map_term f) pguard;
      pnew_goal = option_map (map_sequent f) pnew_goal;
      pamap;
    }

  let map_clause f ({ A.body = { term; amap } } as x) =
    { x with A.body = { term = smart_map_term f term; amap } }

  type subst = (string * C.t -> C.t) option

  let apply_subst f = function
    | None -> fun x -> x
    | Some (_,s) -> fun x -> f s x

  let apply_subst_list f = apply_subst (fun x -> smart_map (f x))

  let apply_subst_constant = apply_subst (fun f x -> f x)

  let apply_subst_types = apply_subst_list smart_map_type

  let apply_subst_modes =
    apply_subst (fun f modes ->
       C.Map.fold (fun c v m -> C.Map.add (f c) v m) modes C.Map.empty)

  let apply_subst_chr = apply_subst_list map_chr

  let apply_subst_clauses = apply_subst_list map_clause
    
  let push_subst extra_prefix symbols_affected subst =
    let oldprefix, oldsubst =
      match subst with Some (p,x) -> p, x | None -> [],fun x -> x in
    let newprefix = oldprefix @ [extra_prefix] in
    let newsubst c =
      if C.Set.mem c symbols_affected then ToDBL.prefix_const newprefix c
      else oldsubst c in
    Some(newprefix, newsubst)

  let rec compile_body lcs types modes clauses chr subst state bl =
    match bl with
    | [] -> types, modes, clauses, chr
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

  let run state
    { StructuredProgram.local_names;
      pbody = { types; modes; body; symbols = _ };
      toplevel_macros;
    }
  =
    let types, modes, clauses, chr =
      compile_body local_names types modes [] [] None state body in
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

  val run : Flat.program -> Flat.program

  (* Exported to compile the query *)
  val spill_preterm :
    (bool * type_declaration) list -> mode C.Map.t -> preterm -> preterm

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
      let _, { ttype } = List.find (fun (_,{ tname }) -> tname == c) types in
      read_ty ttype.term
    with
      Not_found -> `Unknown

  let missing_args_of modes types t =
    let c, args =
      match t with
      | App (c,x,xs) -> c, x :: xs
      | Const c -> c, []
      | Builtin(c,args) -> c, args
      | _ -> error ("only applications can be spilled: " ^ show_term t) in
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
            error Printf.(sprintf
              "cannot spill %s: only %d out of %d missing arguments are output"
              (show_term t) output_suffix missing);
          missing
      | _ -> error ("cannot spill, unknown arity of " ^ C.show c) in
    if missing_args <= 0 then
      error ("cannot spill fully applied " ^ show_term t);
    missing_args

  let spill_term modes types argmap term =

    let argmap = ref argmap in
    let mk_Arg n =
      let m, (x,_) = mk_Arg n !argmap in
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

    let add_spilled ~under_lam sp t =
      if sp = [] then t else
      if under_lam then error "spilling under anonymous clause is not supported"
      else mkAppC C.andc (List.map snd sp @ [t]) in

    let rec spaux (depth,vars,under_lam as ctx) = function
      | App(c, fcall, rest) when c == C.spillc ->
         assert (rest = []);
         let spills, fcall = spaux1 ctx fcall in
         let args =
            mkSpilled (List.rev vars) (missing_args_of modes types fcall) in
         spills @ [args, mkApp fcall args], args
      | App(c, Lam arg, []) when c == C.pic ->
         let ctx = depth+1, mkConst depth :: vars, under_lam in
         let spills, arg = spaux1 ctx arg in
         [], [mkAppC c [Lam (add_spilled ~under_lam spills arg)]]
      | App(c, Lam arg, []) when c == C.sigmac ->
         let ctx = depth+1, vars, under_lam in
         let spills, arg = spaux1 ctx arg in
         [], [mkAppC c [Lam (add_spilled ~under_lam spills arg)]]
      | App(c, hyp, [concl]) when c == C.implc ->
         let spills_hyp, hyp1 = spaux1 ctx hyp in
         let t = spaux1_prop ctx concl in
         if (spills_hyp != []) then
           error ("Cannot spill in the head of a clause: " ^ show_term hyp);
         [], [mkAppC c (hyp1 :: t)]
      | App(c, concl, [hyp]) when c == C.rimplc ->
         let t = spaux1_prop ctx hyp in
         let spills_concl, concl1 = spaux1 ctx concl in
         if (spills_concl != []) then
           error ("Cannot spill in the head of a clause: " ^ show_term concl);
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
         if is_prop then [], [add_spilled ~under_lam spills (mkAppC hd args)]
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
         [], [add_spilled ~under_lam spills (Builtin(c,List.concat args))]
      | Lam t ->
         let sp, t = spaux1 (depth+1, mkConst depth :: vars, true) t in
         let (t,_), sp = map_acc (fun (t,n) (names, call) ->
               let all_names = names @ n in
               let call = apply_to all_names (mkConst depth) call in
               let t = apply_to names (mkConst depth) t in
               (t,all_names), (names, mkAppC C.pic [Lam call])
           ) (t,[]) sp in
         sp, [Lam t]
      | (UVar _ | AppUVar _ | Arg _ | AppArg _) -> assert false

    and spaux1 ctx t =
      let spills, ts = spaux ctx t in
      if (List.length ts != 1) then
        error ("Spilling: expecting only one term at: " ^ show_term t);
      spills, List.hd ts
    
    and spaux1_prop (_, _, under_lam as ctx) t =
      let spills, ts = spaux ctx t in
      if (List.length ts != 1) then
        error ("Spilling: expecting only one term at: " ^ show_term t);
      [add_spilled ~under_lam spills (List.hd ts)]

    in

    let sp, term = spaux (0,[],false) term in
    assert(List.length term = 1);
    let term = List.hd term in
    assert(sp = []);
    !argmap, term

  let spill_presequent modes types pamap ({ pconclusion } as s) =
    let pamap, pconclusion = spill_term modes types pamap pconclusion in
    pamap, { s with pconclusion }

  let spill_rule modes types ({ pguard; pnew_goal; pamap } as r) =
    let pamap, pguard = option_mapacc (spill_term modes types) pamap pguard in
    let pamap, pnew_goal =
      option_mapacc (spill_presequent modes types) pamap pnew_goal in
    { r with pguard; pnew_goal; pamap }

  let spill_chr modes types (clique, rules) =
    let rules = List.map (spill_rule modes types) rules in
    (clique, rules)

  let spill_clause modes types ({ A.body = { term; amap } } as x) =
    let amap, term = spill_term modes types amap term in
    { x with A.body = { term; amap } }

  let run ({ Flat.clauses; modes; types; chr } as p) =
    let clauses = List.map (spill_clause modes types) clauses in
    let chr = List.map (spill_chr modes types) chr in
    { p with clauses; chr }

  let spill_preterm types modes { term; amap } =
    let amap, term = spill_term modes types amap term in
    { amap; term }

end (* }}} *)

module Assemble : sig

  val run : ?flags:flags -> Flat.program list -> Assembled.program

end = struct (* {{{ *)

  let sort_insertion l =
    let add s { A.attributes = { Assembled.id }; loc } =
      match id with
      | None -> s
      | Some n ->
          if StrMap.mem n s then
            error (Ploc.show loc ^ ": a clause named " ^ n ^
                   " already exists at " ^ Ploc.show (StrMap.find n s))
          else
            StrMap.add n loc s in
    let compile_clause ({ A.attributes = { StructuredAST.id; ifexpr }} as c) =
      { c with attributes = { Assembled.id; ifexpr }}
    in
    let rec insert loc_name c l =
      match l, loc_name with
      | [],_ -> error (Ploc.show c.A.loc ^
           ": unable to graft this clause: no clause named " ^
             match loc_name with
             | StructuredAST.After x -> x
             | StructuredAST.Before x -> x)
      | { A.attributes = { Assembled.id = Some n }} as x :: xs,
        StructuredAST.After name when n = name ->
           c :: x :: xs
      | { A.attributes = { Assembled.id = Some n }} as x :: xs,
        StructuredAST.Before name when n = name ->
           x :: c :: xs
      | x :: xs, _ -> x :: insert loc_name c xs in
    let rec aux seen acc = function
      | [] -> List.rev acc
      | { A.attributes = { StructuredAST.insertion = Some i }} as x :: xs ->
          let x = compile_clause x in
          aux (add seen x) (insert i x acc) xs
      | x :: xs ->
          let x = compile_clause x in
          aux (add seen x) (x :: acc) xs
    in
    aux StrMap.empty  [] l

  let run ?flags pl =
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

let program_of_ast p =
 let p = Preprocessing.run p in
 let s, p = ToDBL.run (CS.init()) p in
 let p = Flatten.run s p in
 let p = Spill.run p in
 let p = Assemble.run [ p ] in
 {
   Program.assembled_program = p;
   compiler_state = s;
 }

let query_of_ast { Program.assembled_program; compiler_state } (loc,t)
=
  let initial_depth = assembled_program.Assembled.local_names in
  let types = assembled_program.Assembled.types in
  let modes = assembled_program.Assembled.modes in
  let active_macros = assembled_program.Assembled.toplevel_macros in
  let state, query =
    ToDBL.preterm_of_ast ~depth:initial_depth active_macros compiler_state t in
  let query = Spill.spill_preterm types modes query in
  {
    Query.types;
    modes;
    clauses = assembled_program.Assembled.clauses;
    chr = assembled_program.Assembled.chr;
    initial_depth;
    query;
    query_loc = loc;
    initial_constraints = CustomConstraint.init state;
  } 

let query_of_term { Program.assembled_program; compiler_state } f =
  let initial_depth = assembled_program.Assembled.local_names in
  let types = assembled_program.Assembled.types in
  let modes = assembled_program.Assembled.modes in
  let active_macros = assembled_program.Assembled.toplevel_macros in
  let state, query =
    ToDBL.preterm_of_function
      ~depth:initial_depth active_macros compiler_state
      (f ~depth:initial_depth) in
  {
    Query.types;
    modes;
    clauses = assembled_program.Assembled.clauses;
    chr = assembled_program.Assembled.chr;
    initial_depth;
    query;
    query_loc = Ploc.dummy;
    initial_constraints = CustomConstraint.init state;
  }
  
let check_all_builtin_are_typed types =
  let all_builtin = Builtin.all () in
  List.iter (fun c ->
    if not (List.exists (fun (b,{ tname }) -> b && tname == c) types) then
      error("Built-in without external type declaration: " ^ C.show c))
   all_builtin;
 let elpi_builtins = [C.cutc;C.declare_constraintc;C.print_constraintsc] in
 List.iter (fun (b,{ tname }) ->
   if b && not (List.memq tname elpi_builtins) then
     if not (List.exists ((==) tname) all_builtin) then
       error("External type declaration without Built-in: " ^ C.show tname)
 ) types
;;

let stack_term_of_preterm ~depth:arg_lvl { term = t; amap = { c2i } } =
  let arg_cst c args =
    if C.Map.mem c c2i then
      let argno = C.Map.find c c2i in
      mkAppArg argno arg_lvl args
    else if args = [] then mkConst c
    else App(c,List.hd args,List.tl args) in
  let rec stack_term_of_preterm = function
    | Const c -> arg_cst  c []
    | App(c,x,xs) -> arg_cst  c (List.map stack_term_of_preterm (x::xs))
    | Lam t -> Lam(stack_term_of_preterm  t)
    | CData _ as x -> x
    | Builtin(c,xs) -> Builtin(c,List.map stack_term_of_preterm xs)
    | UVar _ | AppUVar _ | Arg _ | AppArg _ -> assert false
    | Nil as x -> x
    | Discard as x -> x
    | Cons(x,xs) -> Cons(stack_term_of_preterm x,stack_term_of_preterm xs) in
  stack_term_of_preterm t
;;

module Compiler : sig

  (* Translates preterms in terms and AST clauses into clauses (with a key,
   * subgoals, etc *)

  val run : ?flags:flags -> query -> executable

end = struct (* {{{ *)

let compile_chr depth
  { pto_match; pto_remove; pguard; pnew_goal; pamap }
=
  if depth > 0 then error "CHR: rules and locals are not supported";
  let key_of_sequent { pconclusion } =
    match pconclusion with
    | Const x -> x
    | App(x,_,_) -> x
    | f -> 
       error ("CHR: rule without head symbol, got: "^ show_term f) in
  let stack_term_of_preterm term =
    stack_term_of_preterm ~depth:0 { term; amap = pamap } in
  let stack_sequent_of_presequent { pcontext; pconclusion; peigen } =
    let context = stack_term_of_preterm pcontext in
    let conclusion = stack_term_of_preterm pconclusion in
    let eigen = stack_term_of_preterm peigen in
    { CHR.context; conclusion; eigen } in
  let all_sequents = pto_match @ pto_remove in
  let pattern = List.map key_of_sequent all_sequents in
  { CHR.to_match = List.map stack_sequent_of_presequent pto_match;
        to_remove = List.map stack_sequent_of_presequent pto_remove;
        guard = option_map stack_term_of_preterm pguard;
        new_goal = option_map stack_sequent_of_presequent pnew_goal;
        nargs = pamap.nargs;
        pattern;
      }
;;
  
let compile_clause modes initial_depth
  { A.body = ({ amap = { nargs }} as body) }
=
  let body = stack_term_of_preterm ~depth:0 body in
  let cl, _, morelcs = clausify1 modes ~nargs ~depth:initial_depth body in
  if morelcs <> 0 then error "sigma in a toplevel clause is not supported";
  cl

let rec map_if defs f = function
  | [] -> []
  | ({ A.attributes = { Assembled.ifexpr } } as c) :: rest ->
    match ifexpr with
    | None -> f c :: map_if defs f rest 
    | Some e when StrSet.mem e defs -> f c :: map_if defs f rest
    | Some _ -> map_if defs f rest

let run ?(flags = default_flags)
  {
    Query.types;
    modes;
    clauses;
    chr;
    initial_depth;
    query = ({ amap = { nargs; n2i } } as query);
    initial_constraints;
  }
=

  if not flags.allow_untyped_builtin then
    check_all_builtin_are_typed types;
  (* Real Arg nodes: from "Const '%Arg3'" to "Arg 3" *)
  let chr =
    List.fold_left (fun chr (clique, rules) ->
      let chr, clique = CHR.new_clique clique chr in
      let rules = List.map (compile_chr initial_depth) rules in
      List.fold_left (fun x y -> CHR.add_rule clique y x) chr rules)
    CHR.empty chr in
  let prolog_program =
    make_index
      (map_if flags.defined_variables (compile_clause modes initial_depth)
        clauses) in
  {
    Elpi_data.compiled_program = wrap_prolog_prog prolog_program;
    modes;
    chr;
    initial_depth;
    query_env = Array.make nargs C.dummy;
    initial_goal = stack_term_of_preterm ~depth:initial_depth query;
    initial_constraints;
    assignments_names = n2i;
  }

end (* }}} *)

let executable_of_query = Compiler.run

let term_of_ast ~depth t =
 let argsdepth = depth in
 let state = CS.init () in
(*
 let freevars = C.mkinterval 0 depth 0 in
 let state = update_varmap state (fun cmap ->
    List.fold_left (fun cmap i ->
     F.Map.add (F.from_string (C.show (destConst i))) i cmap
     ) F.Map.empty freevars) in
*)
 let _, pt = ToDBL.preterm_of_ast ~depth A.Func.Map.empty state t in
 let t = stack_term_of_preterm ~depth pt in
 let env = Array.make pt.amap.nargs C.dummy in
 move ~adepth:argsdepth ~from:depth ~to_:depth env t
;;

let pp_query pp fmt {
    Query.types;
    modes;
    clauses;
    chr;
    initial_depth;
    query; } =
  Format.fprintf fmt "@[<v>";
  List.iter (fun { A.body } ->
    Format.fprintf fmt "%a.@;" (pp ~depth:initial_depth)
      (stack_term_of_preterm ~depth:initial_depth body))
  clauses;
  Format.fprintf fmt "?- %a.@;" (pp ~depth:initial_depth)
    (stack_term_of_preterm ~depth:initial_depth query);
  Format.fprintf fmt "@]"
;;

(****************************************************************************
  Quotation (for static checkers, see elpi_quoted_syntax.elpi)
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
  App(c,list_to_lp_list l,[])

let mkQCon ~on_type ?(amap=empty_amap) c =
  try mkConst (C.Map.find c amap.c2i)
  with Not_found ->
    let a = if on_type then tconstc else constc in
    if c < 0 then App(a,Elpi_data.C.of_string (C.show c),[])
    else mkConst (c + amap.nargs)

let quote_preterm ?(on_type=false) { term; amap } =
  let mkQApp = mkQApp ~on_type in
  let mkQCon = mkQCon ~on_type ~amap in
  let rec aux depth term = match term with
    | Const n when on_type && C.show n = "string" -> 
        App(C.ctypec, Elpi_data.C.of_string "string",[])
    | Const n when on_type && C.show n = "int" ->
        App(C.ctypec, Elpi_data.C.of_string "int",[])
    | Const n when on_type && C.show n = "float" ->
        App(C.ctypec, Elpi_data.C.of_string "float",[])
    | App(c,CData s,[])
      when on_type && c == C.ctypec && Elpi_data.C.is_string s -> term
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
    List.map Elpi_data.C.of_string

let quote_clause { A.loc; A.attributes = { Assembled.id }; body } =
  (* horrible hack *)
  let clloc = CData.(A.cloc.cin (loc, id)) in
  let qt = close_w_binder argc (quote_preterm body) body.amap in
  let names = sorted_names_of_argmap body.amap in
  App(clausec,CData clloc,[list_to_lp_list names; qt])
;;

let quote_syntax { Query.clauses; query_loc; query } =
  let names = sorted_names_of_argmap query.amap in
  let clist = List.map quote_clause clauses in
  let q =
    App(clausec,CData CData.(A.cloc.cin (query_loc,Some "query")), 
      [list_to_lp_list names;
       close_w_binder argc (quote_preterm ~on_type:false query) query.amap]) in
  clist, q

let default_checker () = Elpi_parser.parse_program ["elpi-checker.elpi"]

let static_check header
  ?(exec=execute_once) ?(checker=default_checker ()) ?(flags=default_flags)
  ({ Query.types } as q)
=
  let p,q = quote_syntax q in
  let tlist = list_to_lp_list (List.map (fun (_,{ tname; ttype }) ->
    App(C.from_stringc "`:",mkQCon ~on_type:false tname,
      [close_w_binder forallc (quote_preterm ~on_type:true ttype) ttype.amap]))
    types) in
  let checker =
    program_of_ast (header @ checker) in
  let query =
    query_of_term checker (fun ~depth state ->
      assert(depth=0);
      state, App(C.from_stringc "check",list_to_lp_list p,[q;tlist])) in
  let executable =
    executable_of_query
      ~flags:{ flags with allow_untyped_builtin = true }
      query in
  exec executable <> Failure
;;

(* vim: set foldmethod=marker: *)
