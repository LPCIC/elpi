(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_data
open Elpi_runtime_trace_off.Elpi_runtime
open Pp

(******************************************************************************
  "Compiler" from AST to program
 ******************************************************************************)

module A = Elpi_ast

(* Function call spilling: from (g {f x}) to (sigma Y\ f x Y, g Y)
 *
 * Works on AST and needs to know the "types" of functors, i.e. their
 * arity in order to know how many extra arguments needs to be used *)
let spill types modes ast =

  let spilled_name = ref 0 in
  let rec mkSpilledNames n =
    if n == 0 then []
    else begin
      incr spilled_name;
      let name = F.from_string ("Spilled_" ^ string_of_int !spilled_name) in
      name :: mkSpilledNames (n-1)
    end in
  let add_spilled sp ctx t =
    match sp, ctx with
    | [], _ -> t
    | _, [] -> A.(App(Const F.andf, List.map snd sp @ [t]))
    | _ ->
       List.fold_left (fun acc ns ->
           List.fold_left (fun acc n ->
              A.(App(Const F.sigmaf, [Lam (n, acc)])))
           acc ns)
        (A.(App(Const F.andf, List.map snd sp @ [t])))
        (List.map fst sp) in

  let rec apply_to names variable = function
    | A.Const f when List.exists (F.equal f) names ->
        A.App(A.Const f,[variable])
    | (A.Const _ | A.CData _ | A.Quoted _) as x -> x
    | A.Lam(x,t) -> A.Lam(x,apply_to names variable t)
    | A.App(A.Const f,args) when List.exists (F.equal f) names ->
        A.App(A.Const f,List.map (apply_to names variable) args @ [variable])
    | A.App(hd,args) ->
        A.App(apply_to names variable hd,
              List.map (apply_to names variable) args) in

  (* approximation of typing... *)
  let _, prop = Constants.funct_of_ast (F.from_string "prop") in
  let variadic,_ = Constants.funct_of_ast (F.from_string "variadic") in
  let _, any = Constants.funct_of_ast (F.from_string "any") in
  let arrow, _ = Constants.funct_of_ast F.arrowf in
  let rec read_ty = function
    | App(c,x,[y]) when c == variadic -> `Variadic (read_ty x, read_ty y)
    | App(c,x,[y]) when c == arrow -> 
        let x = read_ty x in
        begin match read_ty y with
        | `Arrow(l,c) -> `Arrow (x :: l, c)
        | y -> `Arrow([x], y) end
    | Const _ as x when x == prop -> `Prop
    | Const _ as x when x == any -> `Any
    | _ -> `Unknown in
  let type_of = function
    | (A.CData _|A.App _|A.Lam _|A.Quoted _) -> `Unknown
    | A.Const c ->
       if F.(equal c andf || equal c andf2)
       then `Variadic(`Prop, `Prop)
       else if F.(equal c orf) then `Arrow([`Prop],`Prop)
       else 
         let c, _ =  Constants.funct_of_ast c in
         try
           let { ttype = ty } =
             List.find (fun { tname = t } -> t == c) types in
           read_ty ty
         with
           Not_found -> `Unknown in
  let arity_of types t =
    let (c,_), ty, args =
      match t with
      | A.App (A.Const f as hd,args) ->
           Constants.funct_of_ast f, type_of hd, args
      | A.Const c -> Constants.funct_of_ast c, type_of t, []
      | _ -> error ("only applications can be spilled: " ^ A.show_term t) in
    let nargs = List.length args in
    let missing_args =
      (* XXX This sucks: types and mode declarations should be merged XXX *)
      try
        let arity = match ty with
          | `Arrow(l,_) -> List.length l
          | _ -> raise Not_found
        in
        arity - nargs 
      with Not_found ->
        match Constants.Map.find c modes with
        | Mono l ->
            let arity = List.length l in
            let missing = arity - nargs in
            let output_suffix =
              let rec aux = function false :: l -> 1 + aux l | _ -> 0 in
              aux (List.rev l) in
            if missing > output_suffix then
              error Printf.(sprintf
              "cannot spill %s: only %d out of %d missing arguments are outputs"
              (A.show_term t) output_suffix missing);
            missing
        | Multi _ -> error ("cannot spill multi mode relation " ^ Constants.show c)
        | exception Not_found ->
           error ("cannot spill, unknown arity of " ^ Constants.show c) in
    if missing_args <= 0 then
      error ("cannot spill fully applied " ^ A.show_term t);
    missing_args in

  let rec spaux ctx = function
    | A.App(A.Const c,fcall :: rest) when F.(equal c spillf) ->
       assert (rest = []);
       let spills, fcall = spaux1 ctx fcall in
       let ns = mkSpilledNames (arity_of types fcall) in
       let args = List.map (fun x -> A.Const x) ns in
       spills @ [ns, A.mkApp (fcall :: rest @ args)], args
    | A.App(A.Const c, [A.Lam (n,arg)])
      when F.(List.exists (equal c) [pif;sigmaf]) ->
       let spills, arg = spaux1 (n::ctx) arg in
       [], [A.App(A.Const c, [A.Lam (n,add_spilled spills (n::ctx) arg)])]
    | A.App(A.Const c, [hyp; concl]) when F.(equal c implf) ->
       let spills_hyp, hyp1 = spaux1 ctx hyp in
       let t = spaux1_prop ctx concl in
       if (spills_hyp != []) then
         error ("Cannot spill in the head of a clause: " ^ A.show_term hyp);
       [], [A.App(A.Const c, hyp1 :: t)]
    | A.App(A.Const c, [concl;hyp]) when F.(equal c rimplf) ->
       let t = spaux1_prop ctx hyp in
       let spills_concl, concl1 = spaux1 ctx concl in
       if (spills_concl != []) then
         error ("Cannot spill in the head of a clause: " ^ A.show_term concl);
       [], [A.App(A.Const c, concl1 :: t)]
    | A.App(hd,args) ->
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
           aux (type_of hd) args in
       if is_prop then [], [add_spilled spills ctx (A.App(hd, args))]
       else spills, [A.App(hd,args)]
    | (A.CData _ | A.Const _ | A.Quoted _) as x -> [],[x]
    | A.Lam(x,t) ->
       let sp, t = spaux1 (x::ctx) t in
       let (t,_), sp = map_acc (fun (t,n) (names, call) ->
             let all_names = names @ n in
             let call = apply_to all_names (A.Const x) call in
             let t = apply_to names (A.Const x) t in
             (t,all_names), (names, A.App(A.Const F.pif,[A.Lam(x,call)]))
         ) (t,[]) sp in
       sp, [A.Lam (x,t)]

  and spaux1 ctx t =
    let spills, ts = spaux ctx t in
    if (List.length ts != 1) then
      error ("Spilling: expecting only one term at: " ^ Elpi_ast.show_term t);
    spills, List.hd ts
  
  and spaux1_prop ctx t =
    let spills, ts = spaux ctx t in
    if (List.length ts != 1) then
      error ("Spilling: expecting only one term at: " ^ Elpi_ast.show_term t);
    [add_spilled spills ctx (List.hd ts)]

  in
    let sp, t = spaux [] ast in
    assert(List.length t = 1);
    let t = List.hd t in
    assert(sp = []);
    t
;;

(* To assign Arg (i.e. stack) slots to unif variables in clauses *)
type argmap = {
  max_arg : int;
  name2arg : (term * int) StrMap.t;       (* "X" -> Const "%Arg4", 4 *)
  argc2name : (string * int) Constants.Map.t; (* "%Arg4" -> "X", 4 *)
   (* constant used for symbolic pre-computation, real Arg number *)
  arg2name : string IM.t;
}

let empty_amap = {
  max_arg = 0;
  name2arg = StrMap.empty;
  argc2name = Constants.Map.empty;
  arg2name = IM.empty }

type varmap = term F.Map.t 
type quotation = depth:int -> CompilerState.t -> string -> CompilerState.t * term
let named_quotations = ref StrMap.empty
let default_quotation = ref None

let set_default_quotation f = default_quotation := Some f
let register_named_quotation n f =
  named_quotations := StrMap.add n f !named_quotations

(* compiler state *) 
let varmap =
  CompilerState.declare ~name:"elpi:varmap" ~pp:todopp
    ~init:(fun () -> F.Map.empty)
let get_varmap, set_varmap, update_varmap =
  CompilerState.(get varmap, set varmap, update varmap)
let argmap =
  CompilerState.declare ~name:"elpi:argmap" ~pp:todopp
    ~init:(fun () -> empty_amap)
let get_argmap, set_argmap, update_argmap =
  CompilerState.(get argmap, set argmap, update argmap)
let get_modes, set_modes, update_modes =
  CompilerState.(get modes, set modes, update modes)
let get_chr, set_chr, update_chr =
  CompilerState.(get chr, set chr, update chr)
let get_types, set_types, update_types =
  CompilerState.(get declared_types, set declared_types, update declared_types)
let get_clauses, set_clauses, update_clauses =
  CompilerState.(get clauses_w_info, set clauses_w_info, update clauses_w_info)
let get_macros, set_macros, update_macros =
  CompilerState.(get macros, set macros, update macros)

type cmap = term F.Map.t
type comp_state = {
  lcs : int;
  cur_block : Elpi_ast.clause list;
  (* nesting *)
  clique : CHR.clique option;  
  ctx : (Elpi_ast.clause list * cmap) list;

  state : CompilerState.t;
}

let is_Arg state x =
  let { argc2name } = get_argmap state in
  match x with
  | Const c -> Constants.Map.mem c argc2name
  | App(c,_,_) -> Constants.Map.mem c argc2name
  | _ -> false

(* Steps:
   1. from AST to AST: spilling {f x} -> sigma Y\ f x Y
   2. from AST to TERM:
      - @macro expansion (to enable substitution Args are coded as constants)
      - {{quotations}}
      - desugaring "f x -> y" and "X := f y"
      - bound names -> DB levels
   3. from TERM to TERM: (Const "%Arg4") -> (Arg 4)
*)

let mk_Arg state n =
  let { max_arg; name2arg; arg2name } = get_argmap state in
  let cname = Printf.(sprintf "%%Arg%d" max_arg) in
  let n' = Constants.(from_string cname) in
  let nc = Constants.(from_stringc cname) in
  update_argmap state (fun { name2arg; argc2name } ->
    { max_arg = max_arg+1 ;
      name2arg = StrMap.add n (n',max_arg) name2arg;
      argc2name = Constants.Map.add nc (n,max_arg) argc2name;
      arg2name = IM.add max_arg n arg2name }),
    n', nc

let fresh_Arg =
  let qargno = ref 0 in
  fun state ~name_hint:name ~args ->
    incr qargno;
    let name = Printf.sprintf "_fresh_Arg_%s_%d_" name !qargno in
    let state, t, c = mk_Arg state name in
    match args with
    | [] -> state, name, t
    | x::xs -> state, name, App(c,x,xs)

(* Real Arg nodes: from "Const '%Arg3'" to "Arg 3" *)
let argify state ~depth:arg_lvl t =
  let { argc2name } = get_argmap state in
  let arg_cst c args =
    if Constants.Map.mem c argc2name then
      let _, argno = Constants.Map.find c argc2name in
      mkAppArg argno arg_lvl args
    else if args = [] then Constants.of_dbl c
    else App(c,List.hd args,List.tl args) in
  let rec argify = function
    | Const c -> arg_cst  c []
    | App(c,x,xs) -> arg_cst  c (List.map argify (x::xs))
    | Lam t -> Lam(argify  t)
    | CData _ as x -> x
    | Custom(c,xs) -> Custom(c,List.map argify xs)
    | UVar _ | AppUVar _ | Arg _ | AppArg _ -> assert false
    | Nil as x -> x
    | Discard as x -> x
    | Cons(x,xs) -> Cons(argify x,argify xs) in
  argify t
;;

let stack_term_of_ast ?(inner_call=false) ~depth:arg_lvl state ast =
  let macro = get_macros state in
  let types = get_types state in
  let modes = get_modes state in

  (* XXX desugaring: XXX does not seem to be very useful... XXX
      - "f x -> y :- c" ---> "f x TMP :- TMP = y, c"
      - "X := f y" ---> "f y X"
      *)
  let desugar inner s args =
    let open Elpi_ast in
    let open Func in
    let varname = function Const x -> x | _ -> assert false in
    let last_is_arrow l =
      match List.rev l with
      | App(Const f,[_]) :: _ -> equal f arrowf
      | _ -> false in  
    let chop_last_app l =
      match List.rev l with
      | App(_,[x]) :: xs -> x, List.rev xs
      | _ -> assert false in
    match args with
    | [var;App(Const f,args)] when equal s letf -> f, (args @ [var]) 
    | [var;Const f] when equal s letf -> f, [var] 
    | [App(hd,args); hyps] when equal s rimplf && last_is_arrow args ->
      let res, args = chop_last_app args in
      let var = if inner then mkFreshName () else mkFreshUVar () in
      let args = [App(hd, args @ [var]) ;
                  App(Const andf, [App(Const eqf, [var;res]); hyps])] in
      if inner then pif, [Lam(varname var, App(Const s, args ))]
      else s, args
    | args when not (equal s rimplf) && last_is_arrow args ->
      let res, args = chop_last_app args in
      let var = if inner then mkFreshName () else mkFreshUVar () in
      let args = [App(Const s, args @ [var]) ; App(Const eqf, [var;res])] in
      if inner then pif, [Lam(varname var, App(Const rimplf, args))]
      else rimplf, args
    | _ -> s, args in
 
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
    let { name2arg } = get_argmap state in
    try state, fst (StrMap.find n name2arg)
    with Not_found -> let state, t, _ = mk_Arg state n in state, t in

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
     else if is_custom_declared (fst (Constants.funct_of_ast f)) then
       state, Custom(fst (Constants.funct_of_ast f),[])
     else if CustomFunctorCompilation.is_backtick f then
       CustomFunctorCompilation.compile_backtick state f
     else if CustomFunctorCompilation.is_singlequote f then
       CustomFunctorCompilation.compile_singlequote state f
     else state, snd (Constants.funct_of_ast f)

  
  and aux inner lvl state = function
    | A.Const f when F.(equal f nilf) -> state, Nil
    | A.Const f -> stack_funct_of_ast inner lvl state f
    | A.App(A.Const f, [hd;tl]) when F.(equal f consf) ->
       let state, hd = aux true lvl state hd in
       let state, tl = aux true lvl state tl in
       state, Cons(hd,tl)
    | A.App(A.Const f, tl) ->
       let f, tl = desugar inner f tl in
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
       | App(c,hd1,tl1) -> (* FG: decurrying: is this the right place for it ?? *)
          state, App(c,hd1,tl1@tl)
       | Custom(c,tl1) -> state, Custom(c,tl1@tl)
       | Lam _ -> (* macro with args *)
          state, deref_appuv ~from:lvl ~to_:lvl tl c
       | Discard -> 
          error "Clause shape unsupported: _ cannot be applied"
       | _ -> error "Clause shape unsupported" end
(*
    | A.App (A.Custom f,tl) ->
       let cname = stack_custom_of_ast f in
       let state, rev_tl =
         List.fold_left (fun (state, tl) t ->
            let state, t = aux true lvl state t in
            (state, t::tl))
          (state, []) tl in
       state, Custom(cname, List.rev rev_tl)
*)
    | A.Lam (x,t) when A.Func.(equal x dummyname)->
       let state, t' = aux true (lvl+1) state t in
       state, Lam t'
    | A.Lam (x,t) ->
       let orig_varmap = get_varmap state in
       let state = update_varmap state (F.Map.add x (Constants.of_dbl lvl)) in
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
         unquote ~depth:lvl state data 
    | A.Quoted { A.data; A.kind = Some name } ->
         let unquote = 
           try StrMap.find name !named_quotations
           with Not_found -> anomaly ("No '"^name^"' quotation") in
         unquote ~depth:lvl state data 
    | A.App (A.Quoted _,_) -> type_error "Applied quotation"
  in

  let spilled_ast = spill types modes ast in
  (* arg_lvl is the number of local variables *)
  let state, term_no_args = aux false arg_lvl state spilled_ast in
  let term =
    (* we generate args only in the outermost call (i.e. inner
     * quotations don't argify *)
    if inner_call then term_no_args
    else argify state ~depth:arg_lvl term_no_args in
  state, term
;;

(* BUG: I pass the empty amap, that is plainly wrong.
   Therefore the function only works on meta-closed terms. *)
let term_of_ast ~depth t =
 let argsdepth = depth in
 let freevars = Constants.mkinterval 0 depth 0 in
 let state = CompilerState.init () in
 let state = update_varmap state (fun cmap ->
    List.fold_left (fun cmap i ->
     F.Map.add (F.from_string (Constants.show (destConst i))) i cmap
     ) F.Map.empty freevars) in
 let state, t = stack_term_of_ast ~depth state t in
 let { max_arg = max } = get_argmap state in
 let env = Array.make max Constants.dummy in
 move ~adepth:argsdepth ~from:depth ~to_:depth env t
;;

let clause_of_ast lcs state t =
  let state = set_argmap state empty_amap in
  stack_term_of_ast ~depth:lcs state t 

let names_of_args state =
  let { name2arg } = get_argmap state in
  StrMap.map snd name2arg

let mk_env max = Array.make max Constants.dummy

let query_of_ast { query_depth; compiler_state = state } (qloc,t) =
  let state, qterm = clause_of_ast query_depth state t in
  {
    qloc;
    qnames = names_of_args state;
    qdepth = 0;
    qenv = mk_env (get_argmap state).max_arg;
    qterm;
    qconstraints = CustomConstraint.init state;
  } 
;;

let query_of_term { query_depth; compiler_state = state } f =
  let state = set_argmap state empty_amap in
  let state, qterm = f ~depth:query_depth state in
  {
    qloc = Ploc.dummy;
    qnames = names_of_args state;
    qdepth = 0;
    qenv = mk_env (get_argmap state).max_arg;
    qterm = argify state ~depth:query_depth qterm;
    qconstraints = CustomConstraint.init state;
  } 
 
let lp ~depth state s =
  let _loc, ast = Elpi_parser.parse_goal_from_stream (Stream.of_string s) in
  stack_term_of_ast ~inner_call:true ~depth state ast

let chr_of_ast depth state r =
  if depth > 0 then error "CHR: rules and locals are not supported";
  let state = set_argmap state empty_amap in
  let intern state t = stack_term_of_ast ~depth state t in
  let internArg state f =
    let { name2arg } = get_argmap state in
    match StrMap.find (F.show f) name2arg with
    | (_, n) -> F.show f, n
    | exception Not_found -> error ("CHR: variable expected, got "^ F.show f) in
  let intern_sequent state { A.eigen; context; conclusion } =
    let state, eigen = intern state eigen in
    let state, context = intern state context in
    let state, conclusion = intern state conclusion in
    state, { CHR.eigen; context; conclusion } in
  let key_of_sequent { CHR.conclusion } =
    match conclusion with
    | Const x -> x
    | App(x,_,_) -> x
    | _ -> assert false in
  let arg_occurs argno t =
    let rec arg_occurs = function
      | (Const _ | UVar _ | Discard | CData _ | Nil) -> false
      | Arg(i,_) -> i = argno
      | AppArg(i,args) -> i = argno || List.exists arg_occurs args
      | AppUVar(_,_,args) -> List.exists arg_occurs args
      | App(_,x,xs) -> arg_occurs x || List.exists arg_occurs xs
      | Custom(_,xs) -> List.exists arg_occurs xs
      | Cons(x,y) -> arg_occurs x || arg_occurs y
      | Lam x -> arg_occurs x
    in
      arg_occurs t
  in
  let assert_used_only_in patterns patno (name,argno) =
    List.iteri (fun i { CHR.conclusion; context } ->
      let occurs = arg_occurs argno context || arg_occurs argno conclusion in
      if i <> patno &&occurs then
        error (Printf.sprintf "CHR: Alignment variable %s is used in the %dth pattern instead of the %dth" name i patno);
      if i = patno && not occurs then
        error (Printf.sprintf "CHR: Alignment variable %s (%dth position) is not used in the %dth pattern" name patno patno)) patterns
  in
  let assert_1_key_per_goal kg ngoals =
    let gs = List.map snd kg in
    let uniq_gs = uniq (List.sort compare gs) in
    if List.length gs <> List.length uniq_gs || List.length gs <> ngoals then
      error "CHR: Alignment invalid: 1 and only 1 key per sequent"
  in
  let assert_no_uvar_destructuring l =
    let rec test = function
      | App (c,_,_) when c == Constants.uvc -> true
      | Const c when c == Constants.uvc -> true
      | App (_,x,xs) -> test x || List.exists test xs
      | Lam t -> test t
      | (Const _ | Arg _ | CData _ | Nil | Discard) -> false
      | AppArg (_,l) -> List.exists test l
      | Custom (_,l) -> List.exists test l
      | Cons (t1,t2) -> test t1 || test t2
      | UVar _ | AppUVar _ -> assert false
    in
  if List.exists (fun { CHR.context; conclusion } ->
      test context || test conclusion) l then
    error "CHR: unification variables are represented as (uvar Key Args), you can't use ?? to match them"
  in
  let mk_arg2sequent argsno sequents state =
    let arg_occurs_seq arg { CHR.context; conclusion; eigen } =
      arg_occurs arg context ||
      arg_occurs arg conclusion ||
      arg_occurs arg eigen in 
    let m = ref IM.empty in
    for i = 0 to argsno do
      List.iteri (fun j s ->
        let occ = arg_occurs_seq i s in
        if IM.mem i !m && occ then begin
          let n = IM.find i (get_argmap state).arg2name in
          error (Printf.sprintf "CHR: sequent %d and %d share variable %s"
            j (IM.find i !m) n)
        end;
        if occ then m := IM.add i j !m)
        sequents;
    done;
    !m in
  let state, to_match = map_acc intern_sequent state r.A.to_match in
  let state, to_remove = map_acc intern_sequent state r.A.to_remove in
  let state, guard = option_mapacc intern state r.A.guard in
  let state, new_goal = option_mapacc intern_sequent state r.A.new_goal in
  let nargs = (get_argmap state).max_arg in
  let all_sequents = to_match @ to_remove in
  let nsequents = List.length all_sequents in
  let pattern = List.map key_of_sequent all_sequents in
  let alignment, new_goal =
    if r.A.alignment = [] then begin
      let new_goal = match new_goal with
      | Some ({ CHR.eigen = Discard } as g) ->
          Some { g with CHR.eigen = C.of_int 0 }
      | _ -> new_goal in
      None, new_goal
    end else begin
      begin match new_goal with
      | Some { CHR.eigen } when eigen <> Discard ->
          error"CHR: both alignment directive and explicit eigen variable given in new goal"
      | _ -> ()
      end;
      if List.length r.A.alignment <>
         List.length (uniq (List.sort compare r.A.alignment))
         then error "CHR: alignement with duplicates";
      let keys = List.map (internArg state) r.A.alignment in
      assert_1_key_per_goal (List.mapi (fun i j -> j,i) keys) nsequents;
      List.iteri (assert_used_only_in all_sequents) keys;
      Some { CHR.keys; arg2sequent = mk_arg2sequent nargs all_sequents state },
      new_goal
    end in
  assert_no_uvar_destructuring all_sequents;
  { CHR.to_match; to_remove; guard; new_goal; alignment; nargs; pattern }
;;

let sort_insertion l =
  let rec insert loc name c = function
    | [] -> error ("no clause named " ^ name)
    | { Elpi_ast.id = Some n } as x :: xs when n = name ->
         if loc = `Before then c :: x :: xs
         else x :: c :: xs
    | x :: xs -> x :: insert loc name c xs in
  let rec aux acc = function
    | [] -> acc
    | { Elpi_ast.insert = Some (loc,name) } as x :: xs ->
          aux (insert loc name x acc) xs
    | x :: xs -> aux (acc @ [x]) xs
  in
  aux [] l
;;

let debug_print ?print names t =
  if print = Some `Yes then
    Fmt.eprintf "%a.@;" (uppterm 0 names 0 (mk_env (List.length names))) t;
  if print = Some `Raw then
    Fmt.eprintf "%a.@;" pp_term t
;;

let names_of_qnames names =
  StrMap.bindings names
  |> List.sort (fun (_,x) (_,y) -> compare x y)
  |> List.map fst

let check_all_custom_are_typed state =
  let types = get_types state in
  List.iter (fun c ->
    if not (List.exists (fun { tname } -> tname == c) types) then
      error("External without type declaration: " ^ Constants.show c))
   (all_custom ())

let program_of_ast ?print ?(allow_undeclared_custom_predicates=false) (p : Elpi_ast.decl list) : program =

 let clause_of_ast lcs body state =
   let state = set_argmap state empty_amap in
   let state, t = clause_of_ast lcs state body in
   names_of_args state, (get_argmap state).max_arg, t in

 let clausify_block block lcs state =
   let l = sort_insertion block in
   let clauses, lcs =
     List.fold_left (fun (clauses,lcs) { Elpi_ast.body; id; loc } ->
      let names, nargs, t = clause_of_ast lcs body state in
      let names = names_of_qnames names in
      debug_print ?print names t;
      let moreclauses, _, morelcs = clausify (get_modes state) nargs lcs t in
      let loc = CData.(A.cloc.cin (loc, id)) in
      clauses @ List.(map (fun clbody -> 
         { clloc = loc; clargsname = names; clbody})
        (rev moreclauses)),
      lcs + morelcs (* XXX why morelcs? *)
     ) ([],lcs) l in
   update_clauses state (fun program -> program @ clauses), lcs in

 let lcs, state =
   let rec aux ({ lcs; clique; state; cur_block; ctx } as cs) = function
   | [] ->
       if ctx <> [] then error "Begin without an End";
       let state, lcs = clausify_block cur_block lcs state in
       lcs, state

   | d :: todo ->
      match d with
      | Elpi_ast.Chr r ->
          let clique =
            match clique with
            | None -> error "CH rules allowed only in constraint block"
            | Some c -> c in
          let rule = chr_of_ast lcs state r in
          let state = update_chr state (CHR.add_rule clique rule) in
          aux { cs with state } todo
      | Elpi_ast.Type(is_external,name,typ) ->  (* Check ARITY against MODE *)
          let tname, _ = Constants.funct_of_ast name in
          if is_external && not (is_custom_declared tname) then
            error ("External "^F.show name^" not declared");
          if not(is_external) && is_custom_declared tname then
            error (F.show name^" is external, declare its type as such");
          let _, tnargs, ttype = clause_of_ast lcs typ state in
          let state =
            update_types state (fun x -> { tname; tnargs; ttype} :: x) in
          aux { cs with state } todo
      | Elpi_ast.Clause c ->
          aux { cs with cur_block = cur_block @ [c] } todo
      | Elpi_ast.Begin ->
          aux { cs with cur_block = [] ;
                        ctx = (cur_block,get_varmap state) :: ctx } todo
      | Elpi_ast.Accumulated p ->
         aux cs (p @ todo)
      | Elpi_ast.End ->
         if ctx = [] then error "End without a Begin";
         let state, lcs = clausify_block cur_block lcs state in
         let cur_block, varmap = List.hd ctx in
         let state = set_varmap state varmap in
         let ctx = List.tl ctx in
         aux { cur_block; state; ctx; lcs; clique = None } todo
      | Elpi_ast.Local name ->
         let rel = Constants.of_dbl lcs in
         let state = update_varmap state (F.Map.add name rel) in
         aux {cs with lcs = lcs + 1; state } todo
      | Elpi_ast.Macro(loc, n, body) ->
         if F.Map.mem n (get_macros state) then begin
           let _, old_loc = F.Map.find n (get_macros state) in
           error ("Macro "^Elpi_ast.Func.show n^" declared twice:\n"^
             "first declaration: " ^ Elpi_ast.Ploc.show old_loc ^"\n"^
             "second declaration: " ^ Elpi_ast.Ploc.show loc
           );
         end;
         let state = update_macros state (F.Map.add n (body,loc)) in
         aux { cs with state } todo
      | Elpi_ast.Mode m -> (* Check ARITY against TYPE *)
           let funct_of_ast c =
             try
               match F.Map.find c (get_varmap state) with
               | Const x -> x 
               | _ -> assert false
             with Not_found -> fst (Constants.funct_of_ast c) in
           let state = List.fold_left (fun state (c,l,alias) ->
            let key = funct_of_ast c in
            let mode = l in
            let alias = option_map (fun (x,s) ->
              funct_of_ast x,
              List.map (fun (x,y) -> funct_of_ast x, funct_of_ast y) s) alias
            in
            let open Constants in
            match alias with
            | None -> update_modes state (Map.add key (Mono mode))
            | Some (a,subst) ->
                 let state =
                   update_modes state (Map.add a (Mono mode)) in
                 match Map.find key (get_modes state) with
                 | Mono _ -> assert false
                 | Multi l ->
                     update_modes state (Map.add key (Multi ((a,subst)::l)))
                 | exception Not_found ->
                     update_modes state (Map.add key (Multi [a,subst]))
           ) state m in
           aux { cs with state } todo
      | Elpi_ast.Constraint fl ->
           let funct_of_ast c =
             try
               match F.Map.find c (get_varmap state) with
               | Const x -> x 
               | _ -> assert false
             with Not_found -> fst (Constants.funct_of_ast c) in
          if clique <> None then error "nested constraint";
          let fl = List.map (fun x -> funct_of_ast x) fl in
          let state, clique =
            CompilerState.update_return Elpi_data.chr state (CHR.new_clique fl) in
          let clique = Some clique in
          let ctx = (cur_block, get_varmap state) :: ctx in
          aux { cs with cur_block = []; state; clique; ctx } todo
   in
     aux { lcs = 0; clique = None; ctx = []; cur_block = [];
           state = CompilerState.init () } p
 in
 if not allow_undeclared_custom_predicates then
   check_all_custom_are_typed state;
 let prolog_program =
   make_index (List.map drop_clause_info (get_clauses state)) in
 { 
   query_depth = lcs;
   compiled_program = Elpi_data.wrap_prolog_prog prolog_program; 
   compiler_state = state;
 }
;;

(* ---- Quotes the program and the query, see elpi_quoted_syntax.elpi ---- *)

let constc = Constants.from_stringc "const"
let tconstc = Constants.from_stringc "tconst"
let appc = Constants.from_stringc "app"
let tappc = Constants.from_stringc "tapp"
let lamc = Constants.from_stringc "lam"
let cdatac = Constants.from_stringc "cdata"
let forallc = Constants.from_stringc "forall"
let arrowc = Constants.from_stringc "arrow"
let argc = Constants.from_stringc "arg"
let discardc = Constants.from_stringc "discard"

let mkQApp ~on_type l =
  let c = if on_type then tappc else appc in
  App(c,list_to_lp_list l,[])

let mkQCon ~on_type c vars =
  let a = if on_type then tconstc else constc in
  if c < 0 then App(a,C.of_string (Constants.show c),[])
  else Constants.of_dbl (c + vars)

let quote_term ?(on_type=false) vars term =
  let mkQApp = mkQApp ~on_type in
  let mkQCon = mkQCon ~on_type in
  let rec aux depth term = match term with
    | Const n when on_type && Constants.show n = "string" -> 
        App(Constants.ctypec, C.of_string "string",[])
    | Const n when on_type && Constants.show n = "int" ->
        App(Constants.ctypec, C.of_string "int",[])
    | Const n when on_type && Constants.show n = "float" ->
        App(Constants.ctypec, C.of_string "float",[])
    | App(c,CData s,[]) when on_type && c == Constants.ctypec && C.is_string s -> term
    | App(c,s,[t]) when on_type && c == Constants.arrowc ->
        App(arrowc,aux depth s,[aux depth t])
    | Const n when on_type && Constants.show n = "prop" -> term

    | Const n -> mkQCon n vars
    | Custom(c,[]) -> mkQCon c vars
    | Lam x -> App(lamc,Lam (aux (depth+1) x),[])
    | App(c,x,xs) ->
        mkQApp (mkQCon c vars :: List.(map (aux depth) (x :: xs)))
    | Custom(c,args) -> mkQApp (mkQCon c vars :: List.map (aux depth) args)

    | UVar ({ contents = g }, from, args) when g != Constants.dummy ->
       aux depth (deref_uv ~from ~to_:depth args g)
    | AppUVar ({contents = t}, from, args) when t != Constants.dummy ->
       aux depth (deref_appuv ~from ~to_:depth args t)

    | Arg(id,0) -> Constants.of_dbl id
    | Arg(id,argno) -> mkQApp (Constants.of_dbl id :: Constants.mkinterval vars argno 0)
    | AppArg(id,xs) -> mkQApp (Constants.of_dbl id :: List.map (aux depth) xs)

    | UVar _ | AppUVar _ -> assert false

    | CData _ as x -> App(cdatac,x,[])
    | Cons(hd,tl) -> mkQApp [mkQCon Constants.consc vars; aux depth hd; aux depth tl]
    | Nil -> mkQCon Constants.nilc vars
    | Discard -> mkQCon discardc vars
  in
    aux vars term

    (* FIXME : close_with_pis already exists but unused *)
let rec close_w_binder binder t = function
  | 0 -> t
  | n -> App(binder,Lam (close_w_binder binder t (n-1)),[])

let quote_clause { clloc; clargsname; clbody = { key; args; hyps; vars }} =
  (* horrible hack *)
  let hdc, hd = Constants.funct_of_ast (F.from_string (pp_key key)) in
  let head = match args with
    | [] -> hd
    | x::xs -> App(hdc,x,xs) in
  let t =
    if hyps = [] then quote_term vars head
    else
      mkQApp ~on_type:false [mkQCon ~on_type:false Constants.rimplc vars;
              quote_term vars head;
              mkQApp ~on_type:false 
               (mkQCon ~on_type:false Constants.andc vars ::
                List.map (quote_term vars) hyps)]
  in
  let qt = close_w_binder argc t vars in
  let names = List.map C.of_string clargsname in
  App(Constants.andc,CData clloc,[list_to_lp_list names; qt])
;;

let quote_syntax { compiler_state } { qloc; qnames; qenv; qterm } =
  let names = List.map C.of_string (names_of_qnames qnames) in
  let clauses = get_clauses compiler_state in
  let clist = list_to_lp_list (List.map quote_clause clauses) in
  let q =
    let vars = Array.length qenv in
    App(Constants.andc,CData CData.(A.cloc.cin (qloc,Some "query")), 
      [list_to_lp_list names;
       close_w_binder argc (quote_term ~on_type:false vars qterm) vars]) in
  clist, q

let typecheck ?(extra_checker=[]) ({ compiler_state } as p) q =
  let checker =
    (program_of_ast ~allow_undeclared_custom_predicates:true
       (Elpi_parser.parse_program ("elpi_typechecker.elpi"::extra_checker))) in
  let p,q = quote_syntax p q in
  let tlist = list_to_lp_list (List.map (fun {tname;tnargs;ttype} ->
      App(Constants.from_stringc "`:",mkQCon ~on_type:false tname 0,
        [close_w_binder forallc (quote_term ~on_type:true 0 ttype) tnargs]))
    (get_types compiler_state)) in
  let c = Constants.from_stringc "typecheck-program" in
  let query = {
    qloc = Ploc.dummy;
    qnames = StrMap.empty;
    qdepth = 0;
    qenv = [||];
    qterm = App(c,p,[q;tlist]);
    qconstraints = CustomConstraint.init compiler_state;
  } in
  execute_once checker query <> Failure
;;

