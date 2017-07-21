(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_data
open Elpi_runtime_trace_off.Elpi_runtime
open Pp

(******************************************************************************
  "Compiler" from AST to program
 ******************************************************************************)

let modes = ref Constants.Map.empty

module SM = Map.Make(String)

module A = Elpi_ast

(* Function call spilling: from (g {f x}) to (sigma Y\ f x Y, g Y)
 *
 * Works on AST and needs to know the "types" of functors, i.e. their
 * arity in order to know how many extra arguments needs to be used *)
let spill types ast =

  let arity_of types t =
    let (c,ct), args =
      match t with
      | A.App (A.Const f,args) -> Constants.funct_of_ast f, args
      | A.App (A.Custom f,args) -> Constants.funct_of_ast f, args
      | A.Const c -> Constants.funct_of_ast c, []
      | A.Custom c -> Constants.funct_of_ast c, []
      | _ -> error ("only applications can be spilled: " ^ A.show_term t) in
    let nargs = List.length args in
    let missing_args =
      (* XXX This sucks: types and mode declarations should be merged XXX *)    
      try
        let _,_,ty = List.find (fun (t,_,_) -> t == c) types in
        let rec napp = function App(_,_,[x]) -> 1 + napp x | _ -> 0 in
        napp ty - nargs 
      with Not_found ->
        match Constants.Map.find c !modes with
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

  let spilled_name = ref 0 in
  let rec mkSpilledNames n =
    if n == 0 then []
    else begin
      incr spilled_name;
      let name = F.from_string ("Spilled_" ^ string_of_int !spilled_name) in
      name :: mkSpilledNames (n-1)
    end in
  let add_spilled sp t =
    match sp with
    | [] -> [], [t]
    | _ ->
        let to_spill = map_filter snd sp in
        List.map (fun (x,_) -> x, None) sp,
        [A.(App(Const F.andf, to_spill @ [t]))] in

  let rec mapflat2 f l =
    let l1, l2 = List.(split (map f l)) in
    List.flatten l1, List.flatten l2 in

  let rec spaux toplevel = function
    | A.App(A.Const c,fcall :: rest) when F.(equal c spillf) ->
       let ns = mkSpilledNames (arity_of types fcall) in
       let fspills, fcall = spaux false fcall in
       assert(List.length fcall = 1);
       let fcall = List.hd fcall in
       let spills, args = mapflat2 (spaux false) rest in
       let args = List.map (fun x -> A.Const x) ns in
       fspills @ spills @ [ns,Some (A.mkApp (fcall :: args))], args
    | A.App(A.Const c, args)
       when F.(List.exists (equal c) [andf;andf2;orf;rimplf]) ->
       let spills, args = mapflat2 (spaux true) args in
       assert(map_filter snd spills = []);
       spills, [A.App(A.Const c, args)]
    | A.App(A.Const c, [A.Lam (n,arg)])
       when F.(List.exists (equal c) [pif;sigmaf]) ->
       let spills, arg = spaux true arg in
       assert(List.length arg = 1);
       let arg = List.hd arg in
       assert(map_filter snd spills = []);
       let arg = List.fold_left (fun acc (ns,_) ->
         List.fold_left (fun acc n ->
          A.(App(Const F.sigmaf, [Lam (n, acc)]))) acc ns) arg spills in
       [], [A.App(A.Const c, [A.Lam (n,arg)])]
    | A.App(A.Const c, args)
       when F.(List.exists (equal c) [implf;rimplf]) ->
       let spills, args = mapflat2 (spaux true) args in
       assert(map_filter snd spills = []);
       spills, [A.App(A.Const c, args)]
    | A.App(c,args) ->
       let spills, args = mapflat2 (spaux false) args in
       if toplevel then add_spilled spills (A.App(c, args))
       else spills, [A.App(c,args)]
    | (A.String _|A.Float _|A.Int _
      |A.Const _|A.Custom _|A.Quoted _) as x -> [], [x]
    | A.Lam(x,t) ->
       let sp, t = spaux false t in
       if sp <> [] then error "Not supported yet (spill lambda)";
       assert(List.length t = 1);
       let t = List.hd t in
       [], [A.Lam (x,t)]
  in
    let sp, t = spaux true ast in
    assert(List.length t = 1);
    let t = List.hd t in
    assert(map_filter snd sp = []);
    t
;;

(* To assign Arg (i.e. stack) slots to unif variables in clauses *)
type argmap = {
  max_arg : int;
  name2arg : (term * int) SM.t;       (* "X" -> Const "%Arg4", 4 *)
  argc2name : (string * int) Constants.Map.t; (* "%Arg4" -> "X", 4 *)
   (* constant used for symbolic pre-computation, real Arg number *)
}

let empty_amap = { max_arg = 0; name2arg = SM.empty; argc2name = Constants.Map.empty }

type varmap = term F.Map.t 
type quotation = depth:int -> ExtState.t -> string -> ExtState.t * term
let named_quotations = ref SM.empty
let default_quotation = ref None

let set_default_quotation f = default_quotation := Some f
let register_named_quotation n f =
  named_quotations := SM.add n f !named_quotations
 
let varmap = "elpi:varmap"
let get_varmap, set_varmap, update_varmap =
  ExtState.declare_extension varmap (fun () -> F.Map.empty)
;;
let argmap = "elpi:argmap"
let get_argmap, set_argmap, update_argmap =
  ExtState.declare_extension argmap (fun () -> empty_amap)
;;
let types = "elpi:types"
let get_types, set_types, update_types  =
  ExtState.declare_extension types (fun () -> [])
;;
let macros = "elpi:macros"
let get_macros, set_macros, update_macros =
  ExtState.declare_extension macros (fun () -> F.Map.empty)
;;

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
let stack_term_of_ast ?(inner_call=false) ~depth:arg_lvl state ast =
  let macro = get_macros state in
  let types = get_types state in

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
     ('A' <= c && c <= 'Z') || c = '_' in

  let is_macro_name f = 
     let c = (F.show f).[0] in
     c = '@' in

  let stack_arg_of_ast state n =
    let { name2arg; max_arg } = get_argmap state in
    try state, fst (SM.find n name2arg)
    with Not_found ->
     let cname = Printf.(sprintf "%%Arg%d" max_arg) in
     let n' = Constants.(from_string cname) in
     let nc = Constants.(from_stringc cname) in
     update_argmap state (fun { name2arg; argc2name } ->
       { max_arg = max_arg+1 ;
         name2arg = SM.add n (n',max_arg) name2arg;
         argc2name = Constants.Map.add nc (n,max_arg) argc2name }),
       n' in

  let rec stack_macro_of_ast inner lvl state f =
    try aux inner lvl state (F.Map.find f macro)
    with Not_found -> error ("Undeclared macro " ^ F.show f) 
  
  and stack_funct_of_ast inner curlvl state f =
    try state, F.Map.find f (get_varmap state)
    with Not_found ->
     if is_uvar_name f then
       stack_arg_of_ast state (F.show f)
     else if is_macro_name f then
       stack_macro_of_ast inner curlvl state f
     else state, snd (Constants.funct_of_ast f)

  and stack_custom_of_ast f =
    let cname = fst (Constants.funct_of_ast f) in
    if not (is_custom_declared cname) then warn("No custom named "^F.show f);
    cname
  
  and aux inner lvl state = function
    | A.Const f when F.(equal f nilf) -> state, Nil
    | A.Const f -> stack_funct_of_ast inner lvl state f
    | A.Custom f ->
       let cname = stack_custom_of_ast f in
       state, Custom (cname, [])
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
       | Lam _ -> (* macro with args *)
          state, deref_appuv ~from:lvl ~to_:lvl tl c
       | _ -> error "Clause shape unsupported" end
    | A.App (A.Custom f,tl) ->
       let cname = stack_custom_of_ast f in
       let state, rev_tl =
         List.fold_left (fun (state, tl) t ->
            let state, t = aux true lvl state t in
            (state, t::tl))
          (state, []) tl in
       state, Custom(cname, List.rev rev_tl)
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
    | A.String str -> state, CData (in_string str)
    | A.Int i -> state, CData (in_int i)
    | A.Float f -> state, CData (in_float f)
    | A.App (A.Lam _,_) -> error "Beta-redexes not in our language"
    | A.App (A.String _,_) -> type_error "Applied string value"
    | A.App (A.Int _,_) -> type_error "Applied integer value"
    | A.App (A.Float _,_) -> type_error "Applied float value"
    | A.Quoted { A.data; A.kind = None } ->
         let unquote =
           option_get ~err:"No default quotation" !default_quotation in
         unquote ~depth:lvl state data 
    | A.Quoted { A.data; A.kind = Some name } ->
         let unquote = 
           try SM.find name !named_quotations
           with Not_found -> anomaly ("No '"^name^"' quotation") in
         unquote ~depth:lvl state data 
    | A.App (A.Quoted _,_) -> type_error "Applied quotation"
  in

  (* Real Arg nodes: from "Const '%Arg3'" to "Arg 3" *)
  let argify { argc2name } t =
    let arg_cst amap c args =
      if Constants.Map.mem c amap then
        let _, argno = Constants.Map.find c amap in
        mkAppArg argno arg_lvl args
      else if args = [] then Constants.of_dbl c
      else App(c,List.hd args,List.tl args) in
    let rec argify amap = function
      | Const c -> arg_cst amap c []
      | App(c,x,xs) -> arg_cst amap c (List.map (argify amap) (x::xs))
      | Lam t -> Lam(argify amap t)
      | CData _ as x -> x
      | Custom(c,xs) -> Custom(c,List.map (argify amap) xs)
      | UVar _ | AppUVar _ | Arg _ | AppArg _ -> assert false
      | Nil as x -> x
      | Cons(x,xs) -> Cons(argify amap x,argify amap xs) in
    argify argc2name t
  in

  let spilled_ast = spill types ast in
  (* arg_lvl is the number of local variables *)
  let state, term_no_args = aux false arg_lvl state spilled_ast in
  let term =
    (* we generate args only in the outermost call (i.e. inner
     * quotations don't argify *)
    if inner_call then term_no_args
    else argify (get_argmap state) term_no_args in
  state, term
;;

(* BUG: I pass the empty amap, that is plainly wrong.
   Therefore the function only works on meta-closed terms. *)
let term_of_ast ~depth t =
 let argsdepth = depth in
 let freevars = Constants.mkinterval 0 depth 0 in
 let state = ExtState.init () in
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
  let { name2arg = l } = get_argmap state in
  let l = SM.bindings l in
  let l = List.sort (fun (_,(_,x)) (_,(_,y)) -> compare x y) l in
  List.map fst l
;;

let env_of_args state =
  let { max_arg = max } = get_argmap state in
  Array.make max Constants.dummy
;;

let query_of_ast { query_depth = lcs } (loc,t) =
  let state = ExtState.init () in
  let state, clause = clause_of_ast lcs state t in
  loc, names_of_args state, 0, env_of_args state, clause
;;
 
let lp ~depth state s =
  let _loc, ast = Elpi_parser.parse_goal_from_stream (Stream.of_string s) in
  stack_term_of_ast ~inner_call:true ~depth state ast


(* We check no (?? X L) patter is there *)
let assert_no_uvar_destructuring l =
  let rec test = function (* TODO: use generic iterator *)
    | App (c,_,_) when c == Constants.uvc -> true
    | App (_,x,xs) -> test x || List.exists test xs
    | Const _ -> false
    | Lam t -> test t
    | Arg _ -> false
    | AppArg (_,l) -> List.exists test l
    | UVar _ | AppUVar _ -> assert false
    | Custom (_,l) -> List.exists test l
    | CData _ -> false
    | Nil -> false
    | Cons (t1,t2) -> test t1 || test t2
  in
  if List.exists (fun (x,y) -> test x || test y) l then
    error "Variable can only be introspected (eg ?? X L) in the guard"
;;

let chr_of_ast depth state r =
  let state = set_argmap state empty_amap in
  let intern state t = stack_term_of_ast ~depth state t in
  let intern2 state (t1,t2) =
    let state, t1 = intern state t1 in
    let state, t2 = intern state t2 in
    state, (t1,t2) in
  let internArg state f =
    let { name2arg } = get_argmap state in
    match SM.find (F.show f) name2arg with
    | (_, n) -> n
    | exception Not_found -> error "alignement on a non Arg" in
  let state, to_match = map_acc intern2 state r.A.to_match in
  let state, to_remove = map_acc intern2 state r.A.to_remove in
  let state, guard = option_mapacc intern state r.A.guard in
  let state, new_goal = option_mapacc intern state r.A.new_goal in
  let alignement =
    List.map (internArg state) (fst r.A.alignement), snd r.A.alignement in
  let nargs = (get_argmap state).max_arg in
  assert_no_uvar_destructuring (to_match @ to_remove);
  { A.to_match; to_remove; guard; new_goal; alignement; depth; nargs }

type temp = {
  block : (Elpi_ast.term F.Map.t * Elpi_ast.clause) list;
  cmap : term F.Map.t;
  macro : Elpi_ast.term F.Map.t;
}
type comp_state = {
  program : clause_w_info list;
  lcs : int;
  chr : CHR.t;

  tmp : temp;

  (* nesting *)
  clique : CHR.clique option;  
  ctx : temp list;

  (* metadata *)
  types : (constant * int * term) list;
}

let sort_insertion l =
  let rec insert loc name c = function
    | [] -> error ("no clause named " ^ name)
    | (_,{ Elpi_ast.id = Some n }) as x :: xs when n = name ->
         if loc = `Before then c :: x :: xs
         else x :: c :: xs
    | x :: xs -> x :: insert loc name c xs in
  let rec aux acc = function
    | [] -> acc
    | (_,{ Elpi_ast.insert = Some (loc,name) }) as x :: xs ->
          aux (insert loc name x acc) xs
    | x :: xs -> aux (acc @ [x]) xs
  in
  aux [] l
;;

let debug_print ?print state t =
  if print = Some `Yes then
    Fmt.eprintf "%a.@;"
      (uppterm 0 (names_of_args state) 0 (env_of_args state)) t;
  if print = Some `Raw then
    Fmt.eprintf "%a.@;" pp_term t
;;

let program_of_ast ?print (p : Elpi_ast.decl list) : program =
  modes := Constants.Map.empty;

 let clause_of_ast lcs ~cmap ~macro ~types body =
   let state = ExtState.init () in
   let state = set_varmap state cmap in
   let state = set_types state types in
   let state = set_macros state macro in
   let state, t = clause_of_ast lcs state body in
   state, (get_argmap state).max_arg, t in
 let chr_of_ast lcs ~cmap ~macro ~types r =
   let state = ExtState.init () in
   let state = set_varmap state cmap in
   let state = set_types state types in
   let state = set_macros state macro in
   chr_of_ast lcs state r in

 let clausify_block program modes block lcs cmap types =
   let l = sort_insertion block in
   let clauses, lcs =
     List.fold_left (fun (clauses,lcs) (macro,{ Elpi_ast.body; id; loc }) ->
      let state, nargs, t = clause_of_ast lcs ~cmap ~macro ~types body in
      debug_print ?print state t;
      let moreclauses, morelcs = clausify modes nargs lcs t in
      let loc = in_loc (loc, id) in
      let names = names_of_args state in
      clauses @ List.(map (fun clbody -> 
         { clloc = loc; clargsname = names; clbody})
        (rev moreclauses)),
      lcs + morelcs (* XXX why morelcs? *)
     ) ([],lcs) l in
   program @ clauses, lcs in

 let clauses, lcs, chr, types =
   let rec aux ({ program; lcs; chr; clique; types;
                  tmp = ({ block; cmap; macro } as tmp); ctx } as cs) = function
   | [] ->
       if ctx <> [] then error "Begin without an End";
       let program, lcs = clausify_block program !modes block lcs cmap types in
       program, lcs, chr, cs.types

   | d :: todo ->
      match d with
      | Elpi_ast.Chr r ->
          let clique =
            match clique with
            | None -> error "CH rules allowed only in constraint block"
            | Some c -> c in
          let rule = chr_of_ast lcs ~cmap ~macro ~types r in
          let chr = CHR.add_rule clique rule chr in
          aux { cs with chr } todo
      | Elpi_ast.Type(name,typ) ->  (* Check ARITY against MODE *)
          let namec, _ = Constants.funct_of_ast name in
          let _,nargs,typ = clause_of_ast lcs ~cmap ~macro ~types typ in
          aux { cs with types = (namec,nargs,typ) :: types } todo
      | Elpi_ast.Clause c ->
          aux { cs with tmp = { tmp with block = (block @ [macro,c])} } todo
      | Elpi_ast.Begin ->
          aux { cs with tmp = { tmp with block = [] }; ctx = tmp :: ctx } todo
      | Elpi_ast.Accumulated p ->
         aux cs (p @ todo)
      | Elpi_ast.End ->
         if ctx = [] then error "End without a Begin";
         let program,lcs = clausify_block program !modes block lcs cmap types in
         let tmp = List.hd ctx in
         let ctx = List.tl ctx in
         aux { cs with program; tmp; ctx; lcs; clique = None } todo
      | Elpi_ast.Local v ->
         aux {cs with lcs = lcs + 1;
              tmp = { tmp with cmap = F.Map.add v (Constants.of_dbl lcs) cmap }} todo
      | Elpi_ast.Macro(n, body) ->
         aux { cs with tmp = { tmp with macro = F.Map.add n body macro }} todo
      | Elpi_ast.Mode m -> (* Check ARITY against TYPE *)
           let funct_of_ast c =
             try
               match F.Map.find c cmap with
               | Const x -> x 
               | _ -> assert false
             with Not_found -> fst (Constants.funct_of_ast c) in
           List.iter (fun (c,l,alias) ->
            let key = funct_of_ast c in
            let mode = l in
            let alias = option_map (fun (x,s) ->
              funct_of_ast x,
              List.map (fun (x,y) -> funct_of_ast x, funct_of_ast y) s) alias
            in
            match alias with
            | None -> modes := Constants.Map.add key (Mono mode) !modes
            | Some (a,subst) ->
                 modes := Constants.Map.add a (Mono mode) !modes;
                 match Constants.Map.find key !modes with
                 | Mono _ -> assert false
                 | Multi l ->
                     modes := Constants.Map.add key (Multi ((a,subst)::l)) !modes
                 | exception Not_found ->
                     modes := Constants.Map.add key (Multi [a,subst]) !modes
           ) m;
           aux cs todo
      | Elpi_ast.Constraint fl ->
           let funct_of_ast c =
             try
               match F.Map.find c cmap with
               | Const x -> x 
               | _ -> assert false
             with Not_found -> fst (Constants.funct_of_ast c) in
          if clique <> None then error "nested constraint";
          let fl = List.map (fun x -> funct_of_ast x) fl in
          let chr, clique = CHR.new_clique fl chr in
          aux { cs with chr; clique = Some clique;
                        tmp = { block = []; cmap; macro };
                        ctx = { block; cmap; macro } :: ctx } todo
   in
     aux { program = []; lcs = 0; chr = CHR.empty; clique = None;
           tmp = { block = []; cmap = F.Map.empty; macro = F.Map.empty };
           ctx = []; types = [] }
         p
 in
 { query_depth = lcs;
   prolog_program =
     Elpi_data.wrap_prolog_prog (make_index (List.map drop_clause_info clauses));
   chr = CHR.wrap_chr chr;
   modes = !modes;
   declared_types = types;
   clauses_w_info = clauses
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

let quote_syntax
  { clauses_w_info = clauses; declared_types = types }
  (qloc,qn,_,qe,qt)
=
  let clist = list_to_lp_list (List.map quote_clause clauses) in
  let q =
    let names = List.map (fun x -> CData(in_string (F.from_string x))) qn in
    let vars = Array.length qe in
    App(Constants.andc,CData (in_loc (qloc,Some "query")), 
      [list_to_lp_list names;
       close_w_binder argc (quote_term ~on_type:false vars qt) vars]) in
  clist, q

let typecheck ?(extra_checker=[]) ({ declared_types = types } as p) q =
  let checker =
    (program_of_ast
       (Elpi_parser.parse_program ("elpi_typechecker.elpi" :: extra_checker))) in
  let p,q = quote_syntax p q in
  let tlist = list_to_lp_list (List.map (fun (name,n,typ) ->
      App(Constants.from_stringc "`:",mkQCon ~on_type:false name 0,
        [close_w_binder forallc (quote_term ~on_type:true 0 typ) n]))
    types) in
  let c = Constants.from_stringc "typecheck-program" in
  let query = Ploc.dummy,[],0,[||],App(c,p,[q;tlist]) in
  if execute_once checker query = Failure then
    Printf.eprintf "Anomaly: Type checking aborts\n%!"
;;

