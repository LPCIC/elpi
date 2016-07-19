(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: ocaml.ml 14641 2011-11-06 11:59:10Z herbelin $ i*)

(*s Production of Ocaml syntax. *)

open OcamlExtractionTable
open Coq
open Miniml
open Mlutil
open Common


(*s Some utility functions. *)

let pp_tvar id =
  let s = id in
  if String.length s < 2 || s.[1]<>'\''
  then str ("'"^s)
  else str ("' "^s)

let pp_tuple_light status f = function
  | [] -> status,mt ()
  | [x] -> f status true x
  | l ->
     let status,res =
      prlist_with_sep_status status
       (fun () -> str "," ++ spc ()) (fun status -> f status false) l in
     status, pp_par true res

let pp_tuple status f = function
  | [] -> status,mt ()
  | [x] -> f status x
  | l ->
     let status,res =
      prlist_with_sep_status status (fun () -> str "," ++ spc ()) f l in
     status,pp_par true res

let pp_boxed_tuple f = function
  | [] -> mt ()
  | [x] -> f x
  | l -> pp_par true (hov 0 (prlist_with_sep (fun () -> str "," ++ spc ()) f l))

let pp_abst = function
  | [] -> mt ()
  | l  ->
      str "fun " ++ prlist_with_sep (fun () -> str " ") pr_id l ++
      str " ->" ++ spc ()

let pp_parameters l =
  (pp_boxed_tuple pp_tvar l ++ space_if (l<>[]))

(*s Ocaml renaming issues. *)

let keywords =
  List.fold_right Idset.add
  [ "and"; "as"; "assert"; "begin"; "class"; "constraint"; "do";
    "done"; "downto"; "else"; "end"; "exception"; "external"; "false";
    "for"; "fun"; "function"; "functor"; "if"; "in"; "include";
    "inherit"; "initializer"; "lazy"; "let"; "match"; "method";
    "module"; "mutable"; "new"; "object"; "of"; "open"; "or";
    "parser"; "private"; "rec"; "sig"; "struct"; "then"; "to"; "true";
    "try"; "type"; "val"; "virtual"; "when"; "while"; "with"; "mod";
    "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr" ; "unit" ; "_" ; "__" ]
  Idset.empty
;;

set_keywords keywords;;

let pp_open status filename =
 let status,res = modname_of_filename status true filename in
 status, str ("open " ^ res  ^ "\n") ++ fnl ()

(*s The pretty-printer for Ocaml syntax*)

(* Beware of the side-effects of [pp_global] and [pp_modname].
   They are used to update table of content for modules. Many [let]
   below should not be altered since they force evaluation order.
*)

let str_global status k r =
 (*CSC: if is_inline_custom r then find_custom r else*) Common.pp_global status k r

let pp_global status k r =
 let status,res = str_global status k r in
  status,str res

(*CSC
let pp_modname mp = str (Common.pp_module mp)

let is_infix r =
  is_inline_custom r &&
  (let s = find_custom r in
   let l = String.length s in
   l >= 2 && s.[0] = '(' && s.[l-1] = ')')

let get_infix r =
  let s = find_custom r in
  String.sub s 1 (String.length s - 2)
*)

let pp_one_field status _r _i r = pp_global status Term r

let pp_field status r fields i = pp_one_field status r i (List.nth fields i)

let pp_fields status r fields =
 list_map_i_status status (fun status -> pp_one_field status r) 0 fields

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let rec pp_type status par vl t =
  let rec pp_rec status par = function
    | Tmeta _ | Tvar' _ | Taxiom -> assert false
    | Tvar i -> (try status,pp_tvar (List.nth vl (pred i))
		 with _ -> status,(str "'a" ++ int i))
(*CSC:
    | Tglob (r,[a1;a2]) when is_infix r ->
	pp_par par (pp_rec true a1 ++ str (get_infix r) ++ pp_rec true a2)
*)
    | Tglob (r,[]) -> pp_global status Type r
(*CSC:
    | Tglob (IndRef(kn,0),l) when kn = mk_ind "Coq.Init.Specif" "sig" ->
	pp_tuple_light pp_rec l
*)
    | Tglob (r,l) ->
       let status,res = pp_tuple_light status pp_rec l in
       let status,res2 = pp_global status Type r in
       status,res ++ spc () ++ res2
    | Tarr (t1,t2) ->
       let status,res = pp_rec status true t1 in
       let status,res2 = pp_rec status false t2 in
       status,pp_par par (res ++ spc () ++ str "->" ++ spc () ++ res2)
    | Tdummy _ -> status,str "__"
    | Tunknown -> status,str "__"
  in
  let status,res = pp_rec status par t in
   status,hov 0 res

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

let is_ifthenelse = function
(*CSC:
  | [|(r1,[],_);(r2,[],_)|] ->
      (try (find_custom r1 = "true") && (find_custom r2 = "false")
       with Not_found -> false)*)
  | _ -> false

let expr_needs_par = function
  | MLlam _  -> true
  | MLcase (_,_,[|_|]) -> false
  | MLcase (_,_,pv) -> not (is_ifthenelse pv)
  | _        -> false

let rec pp_expr status par env args =
  let par' = args <> [] || par
  and apply st = pp_apply st par args in
  function
    | MLrel n ->
	let id = get_db_name n env in status,apply (pr_id id)
    | MLapp (f,args') ->
	let status,stl = map_status status (fun status -> pp_expr status true env []) args' in
        pp_expr status par env (stl @ args) f
    | MLlam _ as a ->
      	let fl,a' = collect_lams a in
	let fl = List.map id_of_mlid fl in
	let fl,env' = push_vars fl env in
        let status,res = pp_expr status false env' [] a' in
	let st = (pp_abst (List.rev fl) ++ res) in
	status,apply (pp_par par' st)
    | MLletin (id,a1,a2) ->
	let i,env' = push_vars [id_of_mlid id] env in
	let pp_id = pr_id (List.hd i) in
	let status,pp_a1 = pp_expr status false env [] a1 in
	let status,pp_a2 =
         pp_expr status (not par && expr_needs_par a2) env' [] a2 in
        status,
	hv 0
	  (apply
	     (pp_par par'
		(hv 0
		   (hov 2
		      (str "let " ++ pp_id ++ str " =" ++ spc () ++ pp_a1) ++
		    spc () ++ str "in") ++
		 spc () ++ hov 0 pp_a2)))
    | MLglob r ->
	(try
	   let args = list_skipn (projection_arity status r) args in
	   let record = List.hd args in
	   let status,res = pp_global status Term r in
	   status,pp_apply (record ++ str "." ++ res) par (List.tl args)
	 with _ ->
          let status,res = pp_global status Term r in
           status,apply res)
(*CSC:    | MLcons _ as c when is_native_char c -> assert (args=[]); pp_native_char c*)
    | MLcons ({c_kind = Coinductive},r,[]) ->
	assert (args=[]);
        let status,res = pp_global status Cons r in
	status,pp_par par (str "lazy " ++ res)
    | MLcons ({c_kind = Coinductive},r,args') ->
	assert (args=[]);
	let status,tuple =
         pp_tuple status (fun status -> pp_expr status true env []) args' in
        let status,res = pp_global status Cons r in
	status,
        pp_par par (str "lazy (" ++ res ++ spc() ++ tuple ++str ")")
    | MLcons (_,r,[]) ->
	assert (args=[]);
	pp_global status Cons r
    | MLcons ({c_kind = Record fields}, r, args') ->
	assert (args=[]);
        let status,res = pp_fields status r fields in
        let status,res2 =
         map_status status (fun status -> pp_expr status true env []) args' in
	status,pp_record_pat (res, res2)
(*CSC:    | MLcons (_,r,[arg1;arg2]) when is_infix r ->
	assert (args=[]);
	pp_par par
	  ((pp_expr status true env [] arg1) ++ str (get_infix r) ++
	   (pp_expr status true env [] arg2))*)
    | MLcons (_,r,args') ->
	assert (args=[]);
	let status,tuple =
         pp_tuple status (fun status -> pp_expr status true env []) args' in
        let status,res = str_global status Cons r in
	if res = "" (* hack Extract Inductive prod *)
	then status,tuple
	else
         let status,res = pp_global status Cons r in
         status,pp_par par (res ++ spc () ++ tuple)
(*CSC:    | MLcase (_, t, pv) when is_custom_match pv ->
	let mkfun (_,ids,e) =
	  if ids <> [] then named_lams (List.rev ids) e
	  else dummy_lams (ast_lift 1 e) 1
	in
	apply
	  (pp_par par'
	     (hov 2
		(str (find_custom_match pv) ++ fnl () ++
		 prvect (fun tr -> pp_expr status true env [] (mkfun tr) ++ fnl ()) pv
		 ++ pp_expr status true env [] t)))*)
    | MLcase (info, t, pv) ->
	let status,expr = if info.m_kind = Coinductive then
         let status,res = pp_expr status true env [] t in
	  status,(str "Lazy.force" ++ spc () ++ res)
	else
	  (pp_expr status false env [] t)
	in
	(try
	   (* First, can this match be printed as a mere record projection ? *)
	   let fields =
	     match info.m_kind with Record f -> f | _ -> raise Impossible
	   in
	   let (r, ids, c) = pv.(0) in
	   let n = List.length ids in
	   let free_of_patvar a = not (List.exists (ast_occurs_itvl 1 n) a) in
	   let proj_hd status i =
            let status,res = pp_expr status true env [] t in
            let status,res2 = pp_field status r fields i in
             status,res ++ str "." ++ res2
	   in
	   match c with
	     | MLrel i when i <= n ->
                let status,res = proj_hd status (n-i) in
                status,apply (pp_par par' res)
	     | MLapp (MLrel i, a) when (i <= n) && (free_of_patvar a) ->
	       let _ids,env' = push_vars (List.rev_map id_of_mlid ids) env in
               let status,res = proj_hd status (n-i) in
               let status,res2 =
                map_status status (fun status -> pp_expr status true env' []) a
               in
	       status,(pp_apply res par (res2 @ args))
	     | _ -> raise Impossible
	 with Impossible ->
	   (* Second, can this match be printed as a let-in ? *)
	   if Array.length pv = 1 then
	     let status,s1,s2 = pp_one_pat status env info pv.(0) in
             status,
	     apply
	       (hv 0
		  (pp_par par'
		     (hv 0
			(hov 2 (str "let " ++ s1 ++ str " =" ++ spc () ++ expr)
			 ++ spc () ++ str "in") ++
		      spc () ++ hov 0 s2)))
	   else
            let status,res =
             try status,pp_ifthenelse par' env expr pv
             with Not_found ->
              let status,res = pp_pat status env info pv in
               status,
                v 0 (str "match " ++ expr ++ str " with" ++ fnl () ++ res)
            in
	     (* Otherwise, standard match *)
             status,
 	     apply (pp_par par' res))
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix status par env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s ->
	(* An [MLexn] may be applied, but I don't really care. *)
	status,pp_par par (str "assert false" ++ spc () ++ str ("(* "^s^" *)"))
    | MLdummy ->
       status,str "__" (*An [MLdummy] may be applied, but I don't really care.*)
    | MLmagic a ->
       let status,res = pp_expr status true env [] a in
	status,pp_apply (str "Obj.magic") par (res :: args)
    | MLaxiom ->
	status,pp_par par (str "failwith \"AXIOM TO BE REALIZED\"")


and pp_record_pat (fields, args) =
   str "{ " ++
   prlist_with_sep (fun () -> str ";" ++ spc ())
     (fun (f,a) -> f ++ str " =" ++ spc () ++ a)
     (List.combine fields args) ++
   str " }"

and pp_ifthenelse _par _env _expr pv = match pv with
(*CSC:  | [|(tru,[],the);(fal,[],els)|] when
      (find_custom tru = "true") && (find_custom fal = "false")
      ->
      hv 0 (hov 2 (str "if " ++ expr) ++ spc () ++
            hov 2 (str "then " ++
		   hov 2 (pp_expr status (expr_needs_par the) env [] the)) ++ spc () ++
	    hov 2 (str "else " ++
	           hov 2 (pp_expr status (expr_needs_par els) env [] els)))*)
  | _ -> raise Not_found

and pp_one_pat status env info (r,ids,t) =
  let ids,env' = push_vars (List.rev_map id_of_mlid ids) env in
  let status,expr = pp_expr status (expr_needs_par t) env' [] t in
  let status,patt = match info.m_kind with
    | Record fields ->
      let status,res = pp_fields status r fields in
      status,pp_record_pat (res, List.rev_map pr_id ids)
    | _ -> match List.rev ids with
(*CSC:	| [i1;i2] when is_infix r -> pr_id i1 ++ str (get_infix r) ++ pr_id i2*)
	| [] -> pp_global status Cons r
	| ids ->
	  (* hack Extract Inductive prod *)
          let status,res = str_global status Cons r in
	  let status,res2 =
           if res = "" then status,mt()
           else
            let status,res = pp_global status Cons r in
             status, res ++ spc () in
	  status,res2 ++ pp_boxed_tuple pr_id ids
  in
  status, patt, expr

and pp_pat status env info pv =
  let factor_br, factor_set = try match info.m_same with
    | BranchFun ints ->
        let i = Intset.choose ints in
        branch_as_fun info.m_typs pv.(i), ints
    | BranchCst ints ->
        let i = Intset.choose ints in
	ast_pop (branch_as_cst pv.(i)), ints
    | BranchNone -> MLdummy, Intset.empty
  with _ -> MLdummy, Intset.empty
  in
  let last = Array.length pv - 1 in
  let status,res =
  prvecti_status status
    (fun status i x -> if Intset.mem i factor_set then status,mt () else
       let status,s1,s2 = pp_one_pat status env info x in
       status,
       hv 2 (hov 4 (str "| " ++ s1 ++ str " ->") ++ spc () ++ hov 2 s2) ++
       if i = last && Intset.is_empty factor_set then mt () else fnl ())
    pv
  in
  let status,res2 =
   if Intset.is_empty factor_set then status,mt () else
   let par = expr_needs_par factor_br in
   match info.m_same with
     | BranchFun _ ->
         let ids, env' = push_vars [anonymous_name] env in
         let status,res = pp_expr status par env' [] factor_br in
         status,hv 2 (str "| " ++ pr_id (List.hd ids) ++ str " ->" ++ spc () ++
		  hov 2 res)
     | BranchCst _ ->
         let status,res = pp_expr status par env [] factor_br in
          status,hv 2 (str "| _ ->" ++ spc () ++ hov 2 res)
     | BranchNone -> status,mt ()
  in
   status, res ++ res2

and pp_function status env t =
  let bl,t' = collect_lams t in
  let bl,env' = push_vars (List.map id_of_mlid bl) env in
  match t' with
    | MLcase(i,MLrel 1,pv) when
	i.m_kind = Standard (*CSC:&& not (is_custom_match pv)*) ->
	if not (ast_occurs 1 (MLcase(i,MLdummy,pv))) then
          let status,res = pp_pat status env' i pv in
	  status,pr_binding (List.rev (List.tl bl)) ++
       	  str " = function" ++ fnl () ++ v 0 res
	else
          let status,res = pp_pat status env' i pv in
          status,
          pr_binding (List.rev bl) ++
          str " = match " ++ pr_id (List.hd bl) ++ str " with" ++ fnl () ++
	  v 0 res
    | _ ->
          let status,res = pp_expr status false env' [] t' in
          status,
          pr_binding (List.rev bl) ++
	  str " =" ++ fnl () ++ str "  " ++
	  hov 2 res

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix status par env i (ids,bl) args =
 let status,res =
  prvect_with_sep_status status
   (fun () -> fnl () ++ str "and ")
   (fun status (fi,ti) ->
     let status,res = pp_function status env ti in
     status, pr_id fi ++ res)
   (array_map2 (fun id b -> (id,b)) ids bl)
 in
  status,
  pp_par par
    (v 0 (str "let rec " ++ res ++ fnl () ++
	  hov 2 (str "in " ++ pp_apply (pr_id ids.(i)) false args)))

let pp_val status e typ =
 let status,res = pp_type status false [] typ in
  status,
  hov 4 (str "(** val " ++ e ++ str " :" ++ spc ()++res++ str " **)") ++ fnl ()

(*s Pretty-printing of [Dfix] *)

let pp_Dfix status (rv,c,t) =
  let status,names = array_map_status status
    (fun status r -> (*CSC:if is_inline_custom r then mt () else*) pp_global status Term r) rv
  in
  let rec pp status init i =
    if i >= Array.length rv then
      (if init then failwith "empty phrase" else status,mt ())
    else
      let void = false(*CSC:is_inline_custom rv.(i)*) ||
	(not false(*CSC:(is_custom rv.(i))*) && c.(i) = MLexn "UNUSED")
      in
      if void then pp status init (i+1)
      else
	let status,def =
	  (*CSC:if is_custom rv.(i) then str " = " ++ str (find_custom rv.(i))
	  else*) pp_function status (empty_env status) c.(i) in
        let status,res = pp_val status names.(i) t.(i) in
        let status,res2 = pp status false (i+1) in
        status,
	(if init then mt () else fnl ()) ++ res ++
	str (if init then "let rec " else "and ") ++ names.(i) ++ def ++ res2
  in pp status true 0

(*s Pretty-printing of inductive types declaration. *)

let pp_comment s = str "(* " ++ s ++ str " *)"

let pp_one_ind status prefix pl name cnames ctyps =
  let pl = rename_tvars keywords pl in
  let pp_constructor status i typs =
   let status,res =
    prlist_with_sep_status status
     (fun () -> spc () ++ str "* ") (fun status -> pp_type status true pl) typs
   in
    status,
    (if i=0 then mt () else fnl ()) ++
    hov 3 (str "| " ++ cnames.(i) ++
	   (if typs = [] then mt () else str " of ") ++ res) in
  let status,res =
   if Array.length ctyps = 0 then status,str " unit (* empty inductive *)"
   else
    let status,res = prvecti_status status pp_constructor ctyps in
     status, fnl () ++ v 0 res
  in
   status,
   pp_parameters pl ++ str prefix ++ name ++
   str " =" ++ res

let pp_logical_ind packet =
  pp_comment (pr_id packet.ip_typename ++ str " : logical inductive") ++
  fnl () ++
  pp_comment (str "with constructors : " ++
	      prvect_with_sep spc pr_id packet.ip_consnames) ++
  fnl ()

let pp_singleton status packet =
  let status,name = pp_global status Type packet.ip_reference in
  let l = rename_tvars keywords packet.ip_vars in
  let status,res = pp_type status false l (List.hd packet.ip_types.(0)) in
  status,
  hov 2 (str "type " ++ pp_parameters l ++ name ++ str " =" ++ spc () ++
	 res ++ fnl () ++
	 pp_comment (str "singleton inductive, whose constructor was " ++
		     pr_id packet.ip_consnames.(0)))

let pp_record status fields packet =
  let ind = packet.ip_reference in
  let status,name = pp_global status Type ind in
  let status,fieldnames = pp_fields status ind fields in
  let l = List.combine fieldnames packet.ip_types.(0) in
  let pl = rename_tvars keywords packet.ip_vars in
  let status,res =
   prlist_with_sep_status status (fun () -> str ";" ++ spc ())
    (fun status (p,t) ->
      let status,res = pp_type status true pl t in
       status, p ++ str " : " ++ res) l in
  status,
  str "type " ++ pp_parameters pl ++ name ++ str " = { "++ hov 0 res ++ str " }"

let pp_coind pl name =
  let pl = rename_tvars keywords pl in
  pp_parameters pl ++ name ++ str " = " ++
  pp_parameters pl ++ str "__" ++ name ++ str " Lazy.t" ++
  fnl() ++ str "and "

let pp_ind status co ind =
  let prefix = if co then "__" else "" in
  let some = ref false in
  let init= ref (str "type ") in
  let status,names =
    array_map_status status
     (fun status p ->
       if p.ip_logical then status,mt ()
       else pp_global status Type p.ip_reference)
      ind.ind_packets
  in
  let status,cnames =
    array_map_status status
      (fun status p -> if p.ip_logical then status,[||] else
	 array_mapi_status status
          (fun status j _ -> pp_global status Cons p.ip_consreferences.(j))
	   p.ip_types)
      ind.ind_packets
  in
  let rec pp status i =
    if i >= Array.length ind.ind_packets then status,mt ()
    else
      let p = ind.ind_packets.(i) in
      (*CSC:
      let ip = assert false(*CSC: (mind_of_kn kn,i)*) in
      if is_custom (IndRef ip) then pp (i+1)
      else*) begin
	some := true;
	if p.ip_logical then
         let status,res = pp status (i+1) in
          status, pp_logical_ind p ++ res
	else
	  let s = !init in
	  begin
	    init := (fnl () ++ str "and ");
            let status,res =
	      pp_one_ind
	        status prefix p.ip_vars names.(i) cnames.(i) p.ip_types in
            let status,res2 = pp status (i+1) in
              status,
	      s ++
	      (if co then pp_coind p.ip_vars names.(i) else mt ()) ++
              res ++ res2
	  end
      end
  in
  let st = pp status 0 in if !some then st else failwith "empty phrase"


(*s Pretty-printing of a declaration. *)

let pp_mind status i =
  match i.ind_kind with
    | Singleton -> pp_singleton status i.ind_packets.(0)
    | Coinductive -> pp_ind status true i
    | Record fields -> pp_record status fields i.ind_packets.(0)
    | Standard -> pp_ind status false i

let pp_decl status = function
(*CSC:    | Dtype (r,_,_) when is_inline_custom r -> failwith "empty phrase"
    | Dterm (r,_,_) when is_inline_custom r -> failwith "empty phrase"*)
    | Dind i -> pp_mind status i
    | Dtype (r, l, t) ->
        let status,name = pp_global status Type r in
	let l = rename_tvars keywords l in
        let ids, (status, def) =
(*CSC:    try
	    let ids,s = find_type_custom r in
	    pp_string_parameters ids, str "=" ++ spc () ++ str s
	  with Not_found ->*)
	    pp_parameters l,
	    if t = Taxiom then status, str "(* AXIOM TO BE REALIZED *)"
	    else
             let status,res = pp_type status false l t in
              status, str "=" ++ spc () ++ res
	in
	status, hov 2 (str "type " ++ ids ++ name ++ spc () ++ def)
    | Dterm (r, a, t) ->
	let status,name = pp_global status Term r in
	let status,def =
	  (*if is_custom r then str (" = " ^ find_custom r)
	  else*) if is_projection status r then
            status,
	    (prvect str (Array.make (projection_arity status r) " _")) ++
	    str " x = x." ++ name
	  else
           let status,res = pp_function status (empty_env status) a in
            status, res ++ mt ()
	in
	let status,res = pp_val status name t in
         status, res ++ hov 0 (str "let " ++ name ++ def)
    | Dfix (rv,defs,typs) ->
	pp_Dfix status (rv,defs,typs)

let pp_spec status = function
(*  | Sval (r,_) when is_inline_custom r -> failwith "empty phrase"
  | Stype (r,_,_) when is_inline_custom r -> failwith "empty phrase"*)
  | Sind i -> pp_mind status i
  | Sval (r,t) ->
      let status,def = pp_type status false [] t in
      let status,name = pp_global status Term r in
      status, hov 2 (str "val " ++ name ++ str " :" ++ spc () ++ def)
  | Stype (r,vl,ot) ->
      let status, name = pp_global status Type r in
      let l = rename_tvars keywords vl in
      let status, ids, def =
(*CSC:
	try
	  let ids, s = find_type_custom r in
	  pp_string_parameters ids,  str "= " ++ str s
	with Not_found ->*)
	  let ids = pp_parameters l in
	  match ot with
	    | None -> status, ids, mt ()
	    | Some Taxiom -> status, ids, str "(* AXIOM TO BE REALIZED *)"
	    | Some t ->
               let status,res = pp_type status false l t in
                status, ids, str "=" ++ spc () ++ res
      in
      status, hov 2 (str "type " ++ ids ++ name ++ spc () ++ def)

let pp_decl status d =
 try pp_decl status d with Failure "empty phrase" -> status, mt ()
;;
