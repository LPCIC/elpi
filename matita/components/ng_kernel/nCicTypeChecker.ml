(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id: nCicTypeChecker.ml 13149 2016-03-23 19:10:29Z fguidi $ *)

module C = NCic 
module Ref = NReference
module R = NCicReduction
module S = NCicSubstitution 
module U = NCicUtils
module E = NCicEnvironment
(* FG: extension for ELPI *)
module LP = NCicELPI

let log b =
   if b then HLog.error "ELPI validation failed!"
   else HLog.message "ELPI validation OK!"

let total_matita_time = ref 0.0
let total_elpi_time = ref 0.0

let _ = at_exit
 (fun () ->
   prerr_endline ("Matita whole type-checking time: " ^
    string_of_float !total_matita_time) ;
   prerr_endline ("ELPI whole type-checking time: " ^
    string_of_float !total_elpi_time))

let benchmark f g =
 let t0 = Unix.gettimeofday () in
 f () ;
 let t1 = Unix.gettimeofday () in
 g () ;
 let t2 = Unix.gettimeofday () in
 total_matita_time := !total_matita_time +. t1 -. t0 ;
 total_elpi_time := !total_elpi_time +. t2 -. t1
(*FG: end of extension for ELPI *)

exception TypeCheckerFailure of string Lazy.t
exception AssertFailure of string Lazy.t

(*
let raise = function
  | TypeCheckerFailure s as e -> prerr_endline (Lazy.force s); raise e
  | e -> raise e
;;
*)

type recf_entry = 
  | Evil of int (* rno *) 
  | UnfFix of bool list (* fixed arguments *) 
  | Safe
;;

let is_dangerous i l = 
  List.exists (function (j,Evil _) when j=i -> true | _ -> false) l
;;

let is_unfolded i l = 
  List.exists (function (j,UnfFix _) when j=i -> true | _ -> false) l
;;

let is_safe i l =
  List.exists (function (j,Safe) when j=i -> true | _ -> false) l
;;

let get_recno i l = 
  try match List.assoc i l with Evil rno -> rno | _ -> assert false
  with Not_found -> assert false
;;

let get_fixed_args i l = 
  try match List.assoc i l with UnfFix fa -> fa | _ -> assert false
  with Not_found -> assert false
;;

let shift_k e (c,rf,x) = e::c,List.map (fun (k,v) -> k+1,v) rf,x+1;;

(* for debugging only
let string_of_recfuns ~subst ~metasenv ~context l = 
  let pp = status#ppterm ~subst ~metasenv ~context in
  let safe, rest = List.partition (function (_,Safe) -> true | _ -> false) l in
  let dang,unf = List.partition (function (_,UnfFix _)-> false | _->true)rest in
  "\n\tsafes: "^String.concat "," (List.map (fun (i,_)->pp (C.Rel i)) safe) ^
  "\n\tfix  : "^String.concat "," 
   (List.map 
     (function (i,UnfFix l)-> pp(C.Rel i)^"/"^String.concat "," (List.map
       string_of_bool l)
     | _ ->assert false) unf) ^
  "\n\trec  : "^String.concat "," 
   (List.map 
     (function (i,Evil rno)->pp(C.Rel i)^"/"^string_of_int rno
     | _ -> assert false) dang)
;;
*)

let fixed_args bos j n nn =
 let rec aux k acc = function
  | C.Appl (C.Rel i::args) when i-k > n && i-k <= nn ->
     let rec combine l1 l2 =
      match l1,l2 with
         [],[] -> []
       | he1::tl1, he2::tl2 -> (he1,he2)::combine tl1 tl2
       | _::tl, [] -> (false,C.Rel ~-1)::combine tl [] (* dummy term *)
       | [],_::_ -> assert false
     in
     let lefts, _ = HExtlib.split_nth (min j (List.length args)) args in
      List.map (fun ((b,x),i) -> b && x = C.Rel (k-i)) 
       (HExtlib.list_mapi (fun x i -> x,i) (combine acc lefts))
  | t -> U.fold (fun _ k -> k+1) k aux acc t    
 in
  List.fold_left (aux 0) 
   (let rec f = function 0 -> [] | n -> true :: f (n-1) in f j) bos
;;

let debruijn status uri number_of_types ~subst context = 
(* manca la subst! *)
 let rec aux k t =
  match t with
   | C.Meta (i,(s,l)) ->
      (try
        let _,_,term,_ = U.lookup_subst i subst in
        let ts = S.subst_meta status (0,l) term in
        let ts' = aux (k-s) ts in
         if ts == ts' then t else ts'
       with U.Subst_not_found _ ->
        match l with
           C.Ctx l ->
            let l1 = HExtlib.sharing_map (aux (k-s)) l in
            if l1 == l then t else C.Meta (i,(s,C.Ctx l1))
         | _ -> t)
   | C.Const (Ref.Ref (uri1,(Ref.Fix (no,_,_) | Ref.CoFix no))) 
   | C.Const (Ref.Ref (uri1,Ref.Ind (_,no,_))) when NUri.eq uri uri1 ->
      C.Rel (k + number_of_types - no)
   | t -> U.map status (fun _ k -> k+1) k aux t
 in
  aux (List.length context)
;;

let sort_of_prod (status:#NCic.status) ~metasenv ~subst context (name,s) t (t1, t2) =
   let t1 = R.whd status ~subst context t1 in
   let t2 = R.whd status ~subst ((name,C.Decl s)::context) t2 in
   match t1, t2 with
   | C.Sort _, C.Sort C.Prop -> t2
   | C.Sort (C.Type u1), C.Sort (C.Type u2) ->
      C.Sort (C.Type (NCicEnvironment.max u1 u2))
   | C.Sort C.Prop,C.Sort (C.Type _) -> t2
   | C.Meta (_,(_,(C.Irl 0 | C.Ctx []))), C.Sort _ -> t2
   | C.Meta (_,(_,(C.Irl 0 | C.Ctx []))), C.Meta (i,(_,(C.Irl 0 | C.Ctx [])))
   | C.Sort _, C.Meta  (i,(_,(C.Irl 0 | C.Ctx []))) ->
        NCic.Meta (i,(0, C.Irl 0))
   | x, (C.Sort _ | C.Meta (_,(_,(C.Irl 0 | C.Ctx []))))
   | _, x -> 
      let y, context = 
        if x == t1 then s, context else t, ((name,C.Decl s)::context)
      in
      raise (TypeCheckerFailure (lazy (Printf.sprintf
        "%s is expected to be a type, but its type is %s that is not a sort" 
         (status#ppterm ~subst ~metasenv ~context y) 
         (status#ppterm ~subst ~metasenv ~context x))))
;;

(* instantiate_parameters ps (x1:T1)...(xn:Tn)C                             *)
(* returns ((x_|ps|:T_|ps|)...(xn:Tn)C){ps_1 / x1 ; ... ; ps_|ps| / x_|ps|} *)
let rec instantiate_parameters status params c =
  match c, params with
  | c,[] -> c
  | C.Prod (_,_,ta), he::tl -> instantiate_parameters status tl (S.subst status he ta)
  | _,_ -> raise (AssertFailure (lazy "1"))
;;

let specialize_inductive_type_constrs status ~subst context ty_term =
  match R.whd status ~subst context ty_term with
  | C.Const (Ref.Ref (_,Ref.Ind _) as ref)  
  | C.Appl (C.Const (Ref.Ref (_,Ref.Ind _) as ref) :: _ ) as ty ->
      let args = match ty with C.Appl (_::tl) -> tl | _ -> [] in
      let _, leftno, itl, _, i = E.get_checked_indtys status ref in
      let left_args,_ = HExtlib.split_nth leftno args in
      let _,_,_,cl = List.nth itl i in
      List.map 
        (fun (rel,name,ty) -> rel, name, instantiate_parameters status left_args ty) cl
  | _ -> assert false
;;

let specialize_and_abstract_constrs status ~subst r_uri r_len context ty_term =
  let cl = specialize_inductive_type_constrs status ~subst context ty_term in
  let len = List.length context in
  let context_dcl = 
    match E.get_checked_obj status r_uri with
    | _,_,_,_, C.Inductive (_,_,tys,_) -> 
        context @ List.map (fun (_,name,arity,_) -> name,C.Decl arity) tys
    | _ -> assert false
  in
  context_dcl,
  List.map (fun (_,id,ty) -> id, debruijn status r_uri r_len ~subst context ty) cl,
  len, len + r_len
;;

exception DoesOccur;;

let does_not_occur status ~subst context n nn t = 
  let rec aux k _ = function
    | C.Rel m when m > n+k && m <= nn+k -> raise DoesOccur
    | C.Rel m when m <= k || m > nn+k -> ()
    | C.Rel m ->
        (try match List.nth context (m-1-k) with
          | _,C.Def (bo,_) -> aux 0 () (S.lift status (m-k) bo)
          | _ -> ()
         with Failure _ -> assert false)
    | C.Meta (_,(_,(C.Irl 0 | C.Ctx []))) -> (* closed meta *) ()
    | C.Meta (mno,(s,l)) ->
         (try
            (* possible optimization here: try does_not_occur on l and
               perform substitution only if DoesOccur is raised *)
            let _,_,term,_ = U.lookup_subst mno subst in
            aux (k-s) () (S.subst_meta status (0,l) term)
          with U.Subst_not_found _ -> () (*match l with
          | C.Irl len -> if not (n+k >= s+len || s > nn+k) then raise DoesOccur
          | C.Ctx lc -> List.iter (aux (k-s) ()) lc*))
    | t -> U.fold (fun _ k -> k + 1) k aux () t
  in
   try aux 0 () t; true
   with DoesOccur -> false
;;

let rec eat_lambdas (status:#NCic.status) ~subst ~metasenv context n te =
  match (n, R.whd status ~subst context te) with
  | (0, _) -> (te, context)
  | (n, C.Lambda (name,so,ta)) when n > 0 ->
      eat_lambdas status ~subst ~metasenv ((name,(C.Decl so))::context) (n - 1) ta
   | (n, te) ->
      raise (AssertFailure (lazy (Printf.sprintf "eat_lambdas (%d, %s)" n 
        (status#ppterm ~subst ~metasenv ~context te))))
;;

let rec eat_or_subst_lambdas status
  ~subst ~metasenv n te to_be_subst args (context,_,_ as k) 
=
  match n, R.whd status ~subst context te, to_be_subst, args with
  | (n, C.Lambda (_,_,ta),true::to_be_subst,arg::args) when n > 0 ->
      eat_or_subst_lambdas status ~subst ~metasenv (n - 1) (S.subst status arg ta)
       to_be_subst args k
  | (n, C.Lambda (name,so,ta),false::to_be_subst,_::args) when n > 0 ->
      eat_or_subst_lambdas status ~subst ~metasenv (n - 1) ta to_be_subst args
       (shift_k (name,(C.Decl so)) k)
  | (_, te, _, _) -> te, k
;;

let check_homogeneous_call (status:#NCic.status) ~subst context indparamsno n uri reduct tl =
 let last =
  List.fold_left
   (fun k x ->
     if k = 0 then 0
     else
      match R.whd status ~subst context x with
      | C.Rel m when m = n - (indparamsno - k) -> k - 1
      | _ -> raise (TypeCheckerFailure (lazy 
         ("Argument "^string_of_int (indparamsno - k + 1) ^ " (of " ^
         string_of_int indparamsno ^ " fixed) is not homogeneous in "^
         "appl:\n"^ status#ppterm ~context ~subst ~metasenv:[] reduct))))
   indparamsno tl
 in
  if last <> 0 then
   raise (TypeCheckerFailure
    (lazy ("Non-positive occurence in mutual inductive definition(s) [2]"^
     NUri.string_of_uri uri)))
;;

(* Inductive types being checked for positivity have *)
(* indexes x s.t. n < x <= nn.                       *)
let rec weakly_positive status ~subst context n nn uri indparamsno posuri te =
  (*CSC: Not very nice. *)
  let dummy = C.Sort C.Prop in
  (*CSC: to be moved in cicSubstitution? *)
  let rec subst_inductive_type_with_dummy _ = function
    | C.Meta (_,(_,C.Irl _)) as x -> x
    | C.Meta (i,(lift,C.Ctx ls)) -> 
        C.Meta (i,(lift,C.Ctx 
          (List.map (subst_inductive_type_with_dummy ()) ls)))
    | C.Const (Ref.Ref (uri',Ref.Ind (true,0,_))) when NUri.eq uri' uri -> dummy
    | C.Appl ((C.Const (Ref.Ref (uri',Ref.Ind (true,0,lno))))::tl) 
        when NUri.eq uri' uri -> 
          let _, rargs = HExtlib.split_nth lno tl in
          if rargs = [] then dummy else C.Appl (dummy :: rargs)
    | t -> U.map status (fun _ x->x) () subst_inductive_type_with_dummy t
  in
  (* this function has the same semantics of are_all_occurrences_positive
     but the i-th context entry role is played by dummy and some checks
     are skipped because we already know that are_all_occurrences_positive
     of uri in te. *)
  let rec aux context n nn te =
    match R.whd status ~subst context te with
     | t when t = dummy -> true
     | C.Meta (i,lc) ->
        (try
          let _,_,term,_ = U.lookup_subst i subst in
          let t = S.subst_meta status lc term in
           weakly_positive status ~subst context n nn uri indparamsno posuri t
         with U.Subst_not_found _ -> true)
     | C.Appl (te::rargs) when te = dummy ->
        List.for_all (does_not_occur status ~subst context n nn) rargs
     | C.Prod (name,source,dest) when
        does_not_occur status ~subst ((name,C.Decl source)::context) 0 1 dest ->
         (* dummy abstraction, so we behave as in the anonimous case *)
         strictly_positive status ~subst context n nn indparamsno posuri source &&
         aux ((name,C.Decl source)::context) (n + 1) (nn + 1) dest
     | C.Prod (name,source,dest) ->
         does_not_occur status ~subst context n nn source &&
         aux ((name,C.Decl source)::context) (n + 1) (nn + 1) dest
     | _ ->
       raise (TypeCheckerFailure (lazy "Malformed inductive constructor type"))
   in
     aux context n nn (subst_inductive_type_with_dummy () te)

and strictly_positive status ~subst context n nn indparamsno posuri te =
  match R.whd status ~subst context te with
   | t when does_not_occur status ~subst context n nn t -> true
   | C.Meta (i,lc) ->
      (try
        let _,_,term,_ = U.lookup_subst i subst in
        let t = S.subst_meta status lc term in
         strictly_positive status ~subst context n nn indparamsno posuri t
       with U.Subst_not_found _ -> true)
   | C.Rel _ when indparamsno = 0 -> true
   | C.Appl ((C.Rel m)::tl) as reduct when m > n && m <= nn ->
      check_homogeneous_call status ~subst context indparamsno n posuri reduct tl;
      List.for_all (does_not_occur status ~subst context n nn) tl
   | C.Prod (name,so,ta) ->
      does_not_occur status ~subst context n nn so &&
       strictly_positive status ~subst ((name,C.Decl so)::context) (n+1) (nn+1)
        indparamsno posuri ta
   | C.Appl (C.Const (Ref.Ref (uri,Ref.Ind _) as r)::tl) -> 
      let _,paramsno,tyl,_,i = E.get_checked_indtys status r in
      let _,name,ity,cl = List.nth tyl i in
      let ok = List.length tyl = 1 in
      let params, arguments = HExtlib.split_nth paramsno tl in
      let lifted_params = List.map (S.lift status 1) params in
      let cl =
        List.map (fun (_,_,te) -> instantiate_parameters status lifted_params te) cl 
      in
      ok &&
      List.for_all (does_not_occur status ~subst context n nn) arguments &&
      List.for_all 
       (weakly_positive status ~subst ((name,C.Decl ity)::context) (n+1) (nn+1)
         uri indparamsno posuri) cl
   | _ -> false
       
(* the inductive type indexes are s.t. n < x <= nn *)
and are_all_occurrences_positive (status:#NCic.status) ~subst context uri indparamsno i n nn te =
  match R.whd status ~subst context te with
  |  C.Appl ((C.Rel m)::tl) as reduct when m = i ->
      check_homogeneous_call status ~subst context indparamsno n uri reduct tl;
      List.for_all (does_not_occur status ~subst context n nn) tl
  | C.Rel m when m = i ->
      if indparamsno = 0 then
       true
      else
        raise (TypeCheckerFailure
         (lazy ("Non-positive occurence in mutual inductive definition(s) [3]"^
          NUri.string_of_uri uri)))
   | C.Prod (name,source,dest) when
      does_not_occur status ~subst ((name,C.Decl source)::context) 0 1 dest ->
      strictly_positive status ~subst context n nn indparamsno uri source &&
       are_all_occurrences_positive status ~subst 
        ((name,C.Decl source)::context) uri indparamsno
        (i+1) (n + 1) (nn + 1) dest
   | C.Prod (name,source,dest) ->
       if not (does_not_occur status ~subst context n nn source) then
         raise (TypeCheckerFailure (lazy ("Non-positive occurrence in "^
         status#ppterm ~context ~metasenv:[] ~subst te)));
       are_all_occurrences_positive status ~subst ((name,C.Decl source)::context)
        uri indparamsno (i+1) (n + 1) (nn + 1) dest
   | _ ->
     raise
      (TypeCheckerFailure (lazy ("Malformed inductive constructor type " ^
        (NUri.string_of_uri uri))))
;;

exception NotGuarded of string Lazy.t;;

let type_of_branch (status:#NCic.status) ~subst context leftno outty cons tycons = 
 let rec aux liftno context cons tycons =
   match R.whd status ~subst context tycons with
   | C.Const (Ref.Ref (_,Ref.Ind _)) -> C.Appl [S.lift status liftno outty ; cons]
   | C.Appl (C.Const (Ref.Ref (_,Ref.Ind _))::tl) ->
       let _,arguments = HExtlib.split_nth leftno tl in
       C.Appl (S.lift status liftno outty::arguments@[cons])
   | C.Prod (name,so,de) ->
       let cons =
        match S.lift status 1 cons with
        | C.Appl l -> C.Appl (l@[C.Rel 1])
        | t -> C.Appl [t ; C.Rel 1]
       in
        C.Prod (name,so, aux (liftno+1) ((name,(C.Decl so))::context) cons de)
   | t -> raise (AssertFailure 
      (lazy ("type_of_branch, the contructor has type: " ^ status#ppterm
       ~metasenv:[] ~context:[] ~subst:[] t)))
 in
  aux 0 context cons tycons
;;


let rec typeof (status:#NCic.status) ~subst ~metasenv context term =
  let rec typeof_aux context = 
    fun t -> (*prerr_endline (status#ppterm ~metasenv ~subst ~context t);*)
    match t with
    | C.Rel n ->
       (try
         match List.nth context (n - 1) with
         | (_,C.Decl ty) -> S.lift status n ty
         | (_,C.Def (_,ty)) -> S.lift status n ty
        with Failure _ | Invalid_argument _ -> 
          raise (TypeCheckerFailure (lazy ("unbound variable " ^ string_of_int n
            ^" under: " ^ status#ppcontext ~metasenv ~subst context))))
    | C.Sort s -> 
         (try C.Sort (NCicEnvironment.typeof_sort s) 
         with 
         | NCicEnvironment.UntypableSort msg -> raise (TypeCheckerFailure msg)
         | NCicEnvironment.AssertFailure msg -> raise (AssertFailure msg))
    | C.Implicit _ -> raise (AssertFailure (lazy "Implicit found"))
    | C.Meta (n,l) as t -> 
       let canonical_ctx,ty =
        try
         let _,c,_,ty = U.lookup_subst n subst in c,ty
        with U.Subst_not_found _ -> try
         let _,c,ty = U.lookup_meta n metasenv in c, ty
(*          match ty with C.Implicit _ -> assert false | _ -> c,ty *)
        with U.Meta_not_found _ ->
         raise (AssertFailure (lazy (Printf.sprintf
          "%s not found in:\n%s" (status#ppterm ~subst ~metasenv ~context t)
           (status#ppmetasenv ~subst metasenv)
          )))
       in
        check_metasenv_consistency t ~subst ~metasenv context canonical_ctx l;
        S.subst_meta status l ty
    | C.Const ref -> type_of_constant status ref
    | C.Prod (name,s,t) ->
       let sort1 = typeof_aux context s in
       let sort2 = typeof_aux ((name,(C.Decl s))::context) t in
       sort_of_prod status ~metasenv ~subst context (name,s) t (sort1,sort2)
    | C.Lambda (n,s,t) ->
       let sort = typeof_aux context s in
       (match R.whd status ~subst context sort with
       | C.Meta _ | C.Sort _ -> ()
       | _ ->
         raise
           (TypeCheckerFailure (lazy (Printf.sprintf
             ("Not well-typed lambda-abstraction: " ^^
             "the source %s should be a type; instead it is a term " ^^ 
             "of type %s") (status#ppterm ~subst ~metasenv ~context s)
             (status#ppterm ~subst ~metasenv ~context sort)))));
       let ty = typeof_aux ((n,(C.Decl s))::context) t in
         C.Prod (n,s,ty)
    | C.LetIn (n,ty,t,bo) ->
       let ty_t = typeof_aux context t in
       let _ = typeof_aux context ty in
       if not (R.are_convertible status ~metasenv ~subst context ty_t ty) then
         raise 
          (TypeCheckerFailure 
            (lazy (Printf.sprintf
              "The type of %s is %s but it is expected to be %s" 
                (status#ppterm ~subst ~metasenv ~context t) 
                (status#ppterm ~subst ~metasenv ~context ty_t) 
                (status#ppterm ~subst ~metasenv ~context ty))))
       else
         let ty_bo = typeof_aux  ((n,C.Def (t,ty))::context) bo in
         S.subst status ~avoid_beta_redexes:true t ty_bo
    | C.Appl (he::(_::_ as args)) ->
       let ty_he = typeof_aux context he in
       let args_with_ty = List.map (fun t -> t, typeof_aux context t) args in
       eat_prods status ~subst ~metasenv context he ty_he args_with_ty
   | C.Appl _ -> raise (AssertFailure (lazy "Appl of length < 2"))
   | C.Match (Ref.Ref (_,Ref.Ind (_,tyno,_)) as r,outtype,term,pl) ->
      let outsort = typeof_aux context outtype in
      let _,leftno,itl,_,_ = E.get_checked_indtys status r in
      let constructorsno =
        let _,_,_,cl = List.nth itl tyno in List.length cl
      in
      let parameters, arguments =
        let ty = R.whd status ~subst context (typeof_aux context term) in
        let r',tl =
         match ty with
            C.Const (Ref.Ref (_,Ref.Ind _) as r') -> r',[]
          | C.Appl (C.Const (Ref.Ref (_,Ref.Ind _) as r') :: tl) -> r',tl
          | _ ->
             raise 
               (TypeCheckerFailure (lazy (Printf.sprintf
                 "Case analysis: analysed term %s is not an inductive one"
                 (status#ppterm ~subst ~metasenv ~context term)))) in
        if not (Ref.eq r r') then
         raise
          (TypeCheckerFailure (lazy (Printf.sprintf
            ("Case analysys: analysed term type is %s, but is expected " ^^
             "to be (an application of) %s")
            (status#ppterm ~subst ~metasenv ~context ty) 
            (status#ppterm ~subst ~metasenv ~context (C.Const r')))))
        else
         try HExtlib.split_nth leftno tl
         with
          Failure _ ->
           raise (TypeCheckerFailure (lazy (Printf.sprintf 
           "%s is partially applied" 
           (status#ppterm  ~subst ~metasenv ~context ty)))) in
      (* let's control if the sort elimination is allowed: [(I q1 ... qr)|B] *)
      let sort_of_ind_type =
        if parameters = [] then C.Const r
        else C.Appl ((C.Const r)::parameters) in
      let type_of_sort_of_ind_ty = typeof_aux context sort_of_ind_type in
      check_allowed_sort_elimination status ~subst ~metasenv r context
       sort_of_ind_type type_of_sort_of_ind_ty outsort;
      (* let's check if the type of branches are right *)
      if List.length pl <> constructorsno then
       raise (TypeCheckerFailure (lazy ("Wrong number of cases in a match")));
      let j,branches_ok,p_ty, exp_p_ty =
        List.fold_left
          (fun (j,b,old_p_ty,old_exp_p_ty) p ->
            if b then
              let cons = 
                let cons = Ref.mk_constructor j r in
                if parameters = [] then C.Const cons
                else C.Appl (C.Const cons::parameters)
              in
              let ty_p = typeof_aux context p in
              let ty_cons = typeof_aux context cons in
              let ty_branch = 
                type_of_branch status ~subst context leftno outtype cons ty_cons
              in
              j+1, R.are_convertible status ~metasenv ~subst context ty_p ty_branch,
              ty_p, ty_branch
            else
              j,false,old_p_ty,old_exp_p_ty
          ) (1,true,C.Sort C.Prop,C.Sort C.Prop) pl
      in
      if not branches_ok then
        raise
         (TypeCheckerFailure 
          (lazy (Printf.sprintf ("Branch for constructor %s :=\n%s\n"^^
          "has type %s\nnot convertible with %s") 
          (status#ppterm  ~subst ~metasenv ~context
            (C.Const (Ref.mk_constructor (j-1) r)))
          (status#ppterm ~metasenv ~subst ~context (List.nth pl (j-2)))
          (status#ppterm ~metasenv ~subst ~context p_ty) 
          (status#ppterm ~metasenv ~subst ~context exp_p_ty)))); 
      let res = outtype::arguments@[term] in
      R.head_beta_reduce status (C.Appl res)
    | C.Match _ -> assert false

  (* check_metasenv_consistency checks that the "canonical" context of a
     metavariable is consitent - up to relocation via the relocation list l -
     with the actual context *)
  and check_metasenv_consistency 
    ~subst ~metasenv term context canonical_context l 
  =
   match l with
    | shift, C.Irl n ->
       let context = snd (HExtlib.split_nth shift context) in
        let rec compare = function
         | 0,_,[] -> ()
         | 0,_,_::_
         | _,_,[] ->
            raise (AssertFailure (lazy (Printf.sprintf
             "(2) Local and canonical context %s have different lengths"
             (status#ppterm ~subst ~context ~metasenv term))))
         | m,[],_::_ ->
            raise (TypeCheckerFailure (lazy (Printf.sprintf
             "Unbound variable -%d in %s" m 
             (status#ppterm ~subst ~metasenv ~context term))))
         | m,t::tl,ct::ctl ->
            (match t,ct with
                (_,C.Decl t1), (_,C.Decl t2)
              | (_,C.Def (t1,_)), (_,C.Def (t2,_))
              | (_,C.Def (_,t1)), (_,C.Decl t2) ->
                 if not (R.are_convertible status ~metasenv ~subst tl t1 t2) then
                  raise 
                      (TypeCheckerFailure 
                        (lazy (Printf.sprintf 
                      ("Not well typed metavariable local context for %s: " ^^ 
                       "%s expected, which is not convertible with %s")
                      (status#ppterm ~subst ~metasenv ~context term) 
                      (status#ppterm ~subst ~metasenv ~context t2) 
                      (status#ppterm ~subst ~metasenv ~context t1))))
              | _,_ ->
               raise 
                   (TypeCheckerFailure (lazy (Printf.sprintf 
                    ("Not well typed metavariable local context for %s: " ^^ 
                     "a definition expected, but a declaration found")
                    (status#ppterm ~subst ~metasenv ~context term)))));
            compare (m - 1,tl,ctl)
        in
         compare (n,context,canonical_context)
    | shift, lc_kind ->
       (* we avoid useless lifting by shortening the context*)
       let l,context = (0,lc_kind), snd (HExtlib.split_nth shift context) in
       let lifted_canonical_context = 
         let rec lift_metas i = function
           | [] -> []
           | (n,C.Decl t)::tl ->
               (n,C.Decl (S.subst_meta status l (S.lift status i t)))::(lift_metas (i+1) tl)
           | (n,C.Def (t,ty))::tl ->
               (n,C.Def ((S.subst_meta status l (S.lift status i t)),
                          S.subst_meta status l (S.lift status i ty)))::(lift_metas (i+1) tl)
         in
          lift_metas 1 canonical_context in
       let l = U.expand_local_context lc_kind in
       try
        List.iter2 
        (fun t ct -> 
          match (t,ct) with
          | t, (_,C.Def (ct,_)) ->
             (*CSC: the following optimization is to avoid a possibly expensive
                    reduction that can be easily avoided and that is quite
                    frequent. However, this is better handled using levels to
                    control reduction *)
             let optimized_t =
              match t with
              | C.Rel n ->
                  (try
                    match List.nth context (n - 1) with
                    | (_,C.Def (te,_)) -> S.lift status n te
                    | _ -> t
                    with Failure _ -> t)
              | _ -> t
             in
             if not (R.are_convertible status ~metasenv ~subst context optimized_t ct)
             then
               raise 
                 (TypeCheckerFailure 
                   (lazy (Printf.sprintf 
                     ("Not well typed metavariable local context: " ^^ 
                      "expected a term convertible with %s, found %s")
                     (status#ppterm ~subst ~metasenv ~context ct) 
                     (status#ppterm ~subst ~metasenv ~context t))))
          | t, (_,C.Decl ct) ->
              let type_t = typeof_aux context t in
              if not (R.are_convertible status ~metasenv ~subst context type_t ct) then
                raise (TypeCheckerFailure 
                 (lazy (Printf.sprintf 
                  ("Not well typed metavariable local context: "^^
                  "expected a term of type %s, found %s of type %s") 
                  (status#ppterm ~subst ~metasenv ~context ct) 
                  (status#ppterm ~subst ~metasenv ~context t) 
                  (status#ppterm ~subst ~metasenv ~context type_t))))
        ) l lifted_canonical_context 
       with
       | Invalid_argument "List.iter2" ->
          raise (AssertFailure (lazy (Printf.sprintf
           "(1) Local and canonical context %s have different lengths"
           (status#ppterm ~subst ~metasenv ~context term))))

 in 
   typeof_aux context term

and check_allowed_sort_elimination status ~subst ~metasenv r =
  let mkapp he arg =
    match he with
    | C.Appl l -> C.Appl (l @ [arg])
    | t -> C.Appl [t;arg] in
  let rec aux context ind arity1 arity2 =
   let arity1 = R.whd status ~subst context arity1 in
   let arity2 = R.whd status ~subst context arity2 in
     match arity1,arity2 with
      | C.Prod (name,so1,de1), C.Prod (_,so2,de2) ->
         if not (R.are_convertible status ~metasenv ~subst context so1 so2) then
          raise (TypeCheckerFailure (lazy (Printf.sprintf
           "In outtype: expected %s, found %s"
           (status#ppterm ~subst ~metasenv ~context so1)
           (status#ppterm ~subst ~metasenv ~context so2)
           )));
         aux ((name, C.Decl so1)::context)
          (mkapp (S.lift status 1 ind) (C.Rel 1)) de1 de2
      | C.Sort _, C.Prod (name,so,ta) ->
         if not (R.are_convertible status ~metasenv ~subst context so ind) then
          raise (TypeCheckerFailure (lazy (Printf.sprintf
           "In outtype: expected %s, found %s"
           (status#ppterm ~subst ~metasenv ~context ind)
           (status#ppterm ~subst ~metasenv ~context so)
           )));
         (match arity1, R.whd status ~subst ((name,C.Decl so)::context) ta with
           | C.Sort s1, (C.Sort s2 as arity2) ->
               (match NCicEnvironment.allowed_sort_elimination s1 s2 with
               | `Yes -> ()
               | `UnitOnly ->
       (* TODO: we should pass all these parameters since we
        * have them already *)
               let _,leftno,itl,_,i = E.get_checked_indtys status r in
               let itl_len = List.length itl in
               let _,itname,ittype,cl = List.nth itl i in
               let cl_len = List.length cl in
                (* is it a singleton, non recursive and non informative
                   definition or an empty one? *)
                if not
                 (cl_len = 0 ||
                  (itl_len = 1 && cl_len = 1 &&
                   let _,_,constrty = List.hd cl in
                     is_non_recursive_singleton status
                       ~subst r itname ittype constrty &&
                     is_non_informative status ~metasenv ~subst leftno constrty))
                then
                 raise (TypeCheckerFailure (lazy
                  ("Sort elimination not allowed: " ^ 
                   status#ppterm ~metasenv ~subst ~context arity1 
                   ^ " towards "^
                   status#ppterm ~metasenv ~subst ~context arity2
                 ))))
           | _ -> ())
      | _,_ -> ()
  in
   aux 

and eat_prods status ~subst ~metasenv context he ty_he args_with_ty = 
  let rec aux ty_he = function 
  | [] -> ty_he
  | (arg, ty_arg)::tl ->
      match R.whd status ~subst context ty_he with 
      | C.Prod (_,s,t) ->
          if R.are_convertible status ~metasenv ~subst context ty_arg s then
            aux (S.subst status ~avoid_beta_redexes:true arg t) tl
          else
           let indent s = "   " ^ (Str.global_replace (Str.regexp "\n") "\n   " s) in
            raise 
              (TypeCheckerFailure 
                (lazy (Printf.sprintf
                  ("Appl: wrong application of\n%s\nThe argument\n%s\nhas type"^^
                   "\n%s\nbut it should have type \n%s\nContext:\n%s\n")
                  (indent (status#ppterm ~subst ~metasenv ~context he))
                  (indent (status#ppterm ~subst ~metasenv ~context arg))
                  (indent (status#ppterm ~subst ~metasenv ~context ty_arg))
                  (indent (status#ppterm ~subst ~metasenv ~context s))
                  (status#ppcontext ~subst ~metasenv context))))
       | _ ->
          raise 
            (TypeCheckerFailure
              (lazy (Printf.sprintf
                "Appl: %s is not a function, it cannot be applied"
                (status#ppterm ~subst ~metasenv ~context
                 (let res = List.length tl in
                  let eaten = List.length args_with_ty - res in
                   (C.Appl
                    (he::List.map fst
                     (fst (HExtlib.split_nth eaten args_with_ty)))))))))
  in
    aux ty_he args_with_ty

and is_non_recursive_singleton status ~subst (Ref.Ref (uri,_)) iname ity cty =
     let ctx = [iname, C.Decl ity] in
     let cty = debruijn status uri 1 [] ~subst cty in
     let len = List.length ctx in
     let rec aux ctx n nn t =
       match R.whd status ~subst ctx t with
       | C.Prod (name, src, tgt) ->
            does_not_occur status ~subst ctx n nn src &&
             aux ((name, C.Decl src) :: ctx) (n+1) (nn+1) tgt
       | C.Rel k | C.Appl (C.Rel k :: _) when k = nn -> true
       | _ -> assert false
     in
     aux ctx (len-1) len cty

and is_non_informative status ~metasenv ~subst paramsno c =
 let rec aux context c =
   match R.whd status ~subst context c with
    | C.Prod (n,so,de) ->
       let s = typeof status ~metasenv ~subst context so in
       (s = C.Sort C.Prop || 
        match s with C.Sort (C.Type ((`CProp,_)::_)) -> true | _ -> false) && 
       aux ((n,(C.Decl so))::context) de
    | _ -> true in
 let context',dx = NCicReduction.split_prods status ~subst [] paramsno c in
  aux context' dx

and check_mutual_inductive_defs status uri ~metasenv ~subst leftno tyl = 
  (* let's check if the arity of the inductive types are well formed *)
  List.iter (fun (_,_,x,_) -> ignore (typeof status ~subst ~metasenv [] x)) tyl;
  (* let's check if the types of the inductive constructors are well formed. *)
  let len = List.length tyl in
  let tys = List.rev_map (fun (_,n,ty,_) -> (n,(C.Decl ty))) tyl in
  ignore
   (List.fold_right
    (fun (it_relev,_,ty,cl) i ->
       let context,ty_sort = NCicReduction.split_prods status ~subst [] ~-1 ty in
       let sx_context_ty_rev,_ = HExtlib.split_nth leftno (List.rev context) in
       List.iter
         (fun (k_relev,_,te) ->
           let k_relev =
            try snd (HExtlib.split_nth leftno k_relev)
            with Failure _ -> k_relev in
           let te = debruijn status uri len [] ~subst te in
           let context,te = NCicReduction.split_prods status ~subst tys leftno te in
           let _,chopped_context_rev =
            HExtlib.split_nth (List.length tys) (List.rev context) in
           let sx_context_te_rev,_ =
            HExtlib.split_nth leftno chopped_context_rev in
           (try
             ignore (List.fold_left2
              (fun context item1 item2 ->
                let convertible =
                 match item1,item2 with
                   (_,C.Decl ty1),(_,C.Decl ty2) ->
                     R.are_convertible status ~metasenv ~subst context ty1 ty2
                 | (_,C.Def (bo1,ty1)),(_,C.Def (bo2,ty2)) ->
                     R.are_convertible status ~metasenv ~subst context ty1 ty2 &&
                      R.are_convertible status ~metasenv ~subst context bo1 bo2
                 | _,_ -> false
                in
                 if not convertible then
                  raise (TypeCheckerFailure (lazy
                   ("Mismatch between the left parameters of the constructor " ^
                    "and those of its inductive type")))
                 else
                  item1::context
              ) [] sx_context_ty_rev sx_context_te_rev)
            with Invalid_argument "List.fold_left2" -> assert false);
           let con_sort = typeof status ~subst ~metasenv context te in
           (match R.whd status ~subst context con_sort, R.whd status ~subst [] ty_sort with
               (C.Sort (C.Type u1) as s1), (C.Sort (C.Type u2) as s2) ->
                if not (E.universe_leq u1 u2) then
                 raise
                  (TypeCheckerFailure
                    (lazy ("The type " ^ status#ppterm ~metasenv ~subst ~context s1^
                      " of the constructor is not included in the inductive" ^
                      " type sort " ^ status#ppterm ~metasenv ~subst ~context s2)))
             | C.Sort _, C.Sort C.Prop
             | C.Sort _, C.Sort C.Type _ -> ()
             | _, _ ->
                raise
                 (TypeCheckerFailure
                   (lazy ("Wrong constructor or inductive arity shape"))));
           (* let's check also the positivity conditions *)
           if 
             not
               (are_all_occurrences_positive status ~subst context uri leftno
                 (i+leftno) leftno (len+leftno) te) 
           then
             raise
               (TypeCheckerFailure
                 (lazy ("Non positive occurence in "^NUri.string_of_uri
                 uri)))
           else check_relevance status ~subst ~metasenv context k_relev te)
         cl;
        check_relevance status ~subst ~metasenv [] it_relev ty;
        i+1)
    tyl 1)

and check_relevance status ~subst ~metasenv context relevance ty =
  let error context ty =
    raise (TypeCheckerFailure 
     (lazy ("Wrong relevance declaration: " ^ 
     String.concat "," (List.map string_of_bool relevance)^ 
     "\nfor type: "^status#ppterm ~metasenv ~subst ~context ty)))
  in
  let rec aux context relevance ty =
    match R.whd status ~subst context ty with
    | C.Prod (name,so,de) ->
        let sort = typeof status ~subst ~metasenv context so in
        (match (relevance,R.whd status ~subst context sort) with
          | [],_ -> ()
          | false::tl,C.Sort C.Prop -> aux ((name,(C.Decl so))::context) tl de
          | true::_,C.Sort C.Prop
          | false::_,C.Sort _
          | false::_,C.Meta _ -> error context ty
          | true::tl,C.Sort _
          | true::tl,C.Meta _ -> aux ((name,(C.Decl so))::context) tl de
          | _ -> raise (AssertFailure (lazy (Printf.sprintf
                 "Prod: the type %s of the source of %s is not a sort"
                  (status#ppterm ~subst ~metasenv ~context sort)
                  (status#ppterm ~subst ~metasenv ~context so)))))
    | _ -> (match relevance with
      | [] -> ()
      | _::_ -> error context ty)
  in aux context relevance ty

and guarded_by_destructors (status:#NCic.status) r_uri r_len ~subst ~metasenv context recfuns t = 
 let recursor f k t = U.fold shift_k k (fun k () -> f k) () t in
 let rec aux (context, recfuns, x as k) t = 
(*
   prerr_endline ("GB:\n" ^ 
     status#ppcontext ~subst ~metasenv context^
     status#ppterm ~metasenv ~subst ~context t^
       string_of_recfuns ~subst ~metasenv ~context recfuns);
*)
  try
  match t with
  | C.Rel m as t when is_dangerous m recfuns -> 
      raise (NotGuarded (lazy 
        (status#ppterm ~subst ~metasenv ~context t ^ 
         " is a partial application of a fix")))
  | C.Appl ((C.Rel m)::tl) as t when is_dangerous m recfuns ->
     let rec_no = get_recno m recfuns in
     if not (List.length tl > rec_no) then 
       raise (NotGuarded (lazy 
         (status#ppterm ~context ~subst ~metasenv t ^ 
         " is a partial application of a fix")))
     else
       let rec_arg = List.nth tl rec_no in
       if not (is_really_smaller status r_uri r_len ~subst ~metasenv k rec_arg) then 
         raise (NotGuarded (lazy (Printf.sprintf ("Recursive call %s, %s is not"
          ^^ " smaller.\ncontext:\n%s") (status#ppterm ~context ~subst ~metasenv
          t) (status#ppterm ~context ~subst ~metasenv rec_arg)
          (status#ppcontext ~subst ~metasenv context))));
       List.iter (aux k) tl
  | C.Appl ((C.Rel m)::tl) when is_unfolded m recfuns ->
       let fixed_args = get_fixed_args m recfuns in
       HExtlib.list_iter_default2
        (fun x b -> if not b then aux k x) tl false fixed_args
  | C.Rel m ->
     (match List.nth context (m-1) with 
     | _,C.Decl _ -> ()
     | _,C.Def (bo,_) -> aux k (S.lift status m bo))
  | C.Meta _ -> ()
  | C.Appl (C.Const ((Ref.Ref (uri,Ref.Fix (i,recno,_))) as r)::args) ->
      if List.exists (fun t -> try aux k t;false with NotGuarded _ -> true) args
      then
      let fl,_,_ = E.get_checked_fixes_or_cofixes status r in
      let ctx_tys, bos = 
        List.split (List.map (fun (_,name,_,ty,bo) -> (name, C.Decl ty), bo) fl)
      in
      let fl_len = List.length fl in
      let bos = List.map (debruijn status uri fl_len context ~subst) bos in
      let j = List.fold_left min max_int (List.map (fun (_,_,i,_,_)->i) fl) in
      let ctx_len = List.length context in
        (* we may look for fixed params not only up to j ... *)
      let fa = fixed_args bos j ctx_len (ctx_len + fl_len) in
      HExtlib.list_iter_default2
       (fun x b -> if not b then aux k x) args false fa; 
      let context = context@ctx_tys in
      let ctx_len = List.length context in
      let extra_recfuns = 
        HExtlib.list_mapi (fun _ i -> ctx_len - i, UnfFix fa) ctx_tys
      in
      let new_k = context, extra_recfuns@recfuns, x in
      let bos_and_ks = 
        HExtlib.list_mapi
         (fun bo fno ->
          let bo_and_k =
            eat_or_subst_lambdas status ~subst ~metasenv j bo fa args new_k
          in
           if
            fno = i &&
            List.length args > recno &&
            (*case where the recursive argument is already really_smaller *)
            is_really_smaller status r_uri r_len ~subst ~metasenv k
             (List.nth args recno)
           then
            let bo,(context, _, _ as new_k) = bo_and_k in
            let bo, context' =
             eat_lambdas status ~subst ~metasenv context (recno + 1 - j) bo in
            let new_context_part,_ =
             HExtlib.split_nth (List.length context' - List.length context)
              context' in
            let k = List.fold_right shift_k new_context_part new_k in
            let context, recfuns, x = k in
            let k = context, (1,Safe)::recfuns, x in
              bo,k
           else
            bo_and_k
         ) bos
      in
       List.iter (fun (bo,k) -> aux k bo) bos_and_ks
  | C.Match (Ref.Ref (_,Ref.Ind (true,_,_)),outtype,term,pl) as t ->
     (match R.whd status ~subst context term with
     | C.Rel m | C.Appl (C.Rel m :: _ ) as t when is_safe m recfuns || m = x ->
         let ty = typeof status ~subst ~metasenv context term in
         let dc_ctx, dcl, start, stop = 
           specialize_and_abstract_constrs status ~subst r_uri r_len context ty in
         let args = match t with C.Appl (_::tl) -> tl | _ -> [] in
         aux k outtype; 
         List.iter (aux k) args; 
         List.iter2
           (fun p (_,dc) ->
             let rl = recursive_args status ~subst ~metasenv dc_ctx start stop dc in
             let p, k = get_new_safes status ~subst k p rl in
             aux k p) 
           pl dcl
     | _ -> recursor aux k t)
  | t -> recursor aux k t
  with
   NotGuarded _ as exc ->
    let t' = R.whd status ~delta:0 ~subst context t in
    if t = t' then raise exc
    else aux k t'
 in
  try aux (context, recfuns, 1) t
  with NotGuarded s -> raise (TypeCheckerFailure s)

and guarded_by_constructors status ~subst ~metasenv context t indURI indlen nn =
 let rec aux context n nn h te =
  match R.whd status ~subst context te with
   | C.Rel m when m > n && m <= nn -> h
   | C.Rel _ | C.Meta _ -> true
   | C.Sort _
   | C.Implicit _
   | C.Prod _
   | C.Const (Ref.Ref (_,Ref.Ind _))
   | C.LetIn _ -> raise (AssertFailure (lazy "17"))
   | C.Lambda (name,so,de) ->
      does_not_occur status ~subst context n nn so &&
      aux ((name,C.Decl so)::context) (n + 1) (nn + 1) h de
   | C.Appl ((C.Rel m)::tl) when m > n && m <= nn ->
      h && List.for_all (does_not_occur status ~subst context n nn) tl
   | C.Const (Ref.Ref (_,Ref.Con _)) -> true
   | C.Appl (C.Const (Ref.Ref (_, Ref.Con (_,j,paramsno))) :: tl) as t ->
      let ty_t = typeof status ~subst ~metasenv context t in
      let dc_ctx, dcl, start, stop = 
        specialize_and_abstract_constrs status ~subst indURI indlen context ty_t in
      let _, dc = List.nth dcl (j-1) in
(*
        prerr_endline (status#ppterm ~subst ~metasenv ~context:dc_ctx dc);
        prerr_endline (status#ppcontext ~subst ~metasenv dc_ctx);
 *)
      let rec_params = recursive_args status ~subst ~metasenv dc_ctx start stop dc in
      let rec analyse_instantiated_type rec_spec args =
       match rec_spec, args with
       | h::rec_spec, he::args -> 
           aux context n nn h he && analyse_instantiated_type rec_spec args 
       | _,[] -> true
       | _ -> raise (AssertFailure (lazy 
         ("Too many args for constructor: " ^ String.concat " "
         (List.map (fun x-> status#ppterm ~subst ~metasenv ~context x) args))))
      in
      let _, args = HExtlib.split_nth paramsno tl in
      analyse_instantiated_type rec_params args
   | C.Appl ((C.Match (_,out,te,pl))::_) 
   | C.Match (_,out,te,pl) as t ->
       let tl = match t with C.Appl (_::tl) -> tl | _ -> [] in
       List.for_all (does_not_occur status ~subst context n nn) tl &&
       does_not_occur status ~subst context n nn out &&
       does_not_occur status ~subst context n nn te &&
       List.for_all (aux context n nn h) pl
(* IMPOSSIBLE unsless we allow to pass cofix to other fix/cofix as we do for 
   higher order fix in g_b_destructors.

   | C.Const (Ref.Ref (u,(Ref.Fix _| Ref.CoFix _)) as ref)
   | C.Appl(C.Const (Ref.Ref(u,(Ref.Fix _| Ref.CoFix _)) as ref) :: _) as t ->
      let tl = match t with C.Appl (_::tl) -> tl | _ -> [] in
      let fl,_,_ = E.get_checked_fixes_or_cofixes ref in 
      let len = List.length fl in
      let tys = List.map (fun (_,n,_,ty,_) -> n, C.Decl ty) fl in
      List.for_all (does_not_occur status ~subst context n nn) tl &&
      List.for_all
       (fun (_,_,_,_,bo) ->
          aux (context@tys) n nn h (debruijn status u len context bo))
       fl
*)
   | C.Const _
   | C.Appl _ as t -> does_not_occur status ~subst context n nn t
 in
   aux context 0 nn false t
                                                                      
and recursive_args status ~subst ~metasenv context n nn te =
  match R.whd status ~subst context te with
  | C.Rel _ | C.Appl _ | C.Const _ -> []
  | C.Prod (name,so,de) ->
     (not (does_not_occur status ~subst context n nn so)) ::
      (recursive_args status ~subst ~metasenv 
        ((name,(C.Decl so))::context) (n+1) (nn + 1) de)
  | t -> 
     raise (AssertFailure (lazy ("recursive_args:" ^ status#ppterm ~subst
     ~metasenv ~context:[] t)))

and get_new_safes status ~subst (context, recfuns, x as k) p rl =
  match R.whd status ~subst context p, rl with
  | C.Lambda (name,so,ta), b::tl ->
      let recfuns = (if b then [0,Safe] else []) @ recfuns in
      get_new_safes status ~subst 
        (shift_k (name,(C.Decl so)) (context, recfuns, x)) ta tl
  | C.Meta _ as e, _ | e, [] -> e, k
  | _ -> raise (AssertFailure (lazy "Ill formed pattern"))

and is_really_smaller status
  r_uri r_len ~subst ~metasenv (context, recfuns, x as k) te 
=
 match R.whd status ~subst context te with
 | C.Rel m when is_safe m recfuns -> true
 | C.Lambda (name, s, t) ->
    is_really_smaller status r_uri r_len ~subst ~metasenv (shift_k (name,C.Decl s) k) t
 | C.Appl (he::_) ->
    is_really_smaller status r_uri r_len ~subst ~metasenv k he
 | C.Appl [] | C.Implicit _ -> assert false
 | C.Meta _ -> true 
 | C.Match (Ref.Ref (_,Ref.Ind (isinductive,_,_)),_,term,pl) ->
    (match term with
    | C.Rel m | C.Appl (C.Rel m :: _ ) when is_safe m recfuns || m = x ->
        if not isinductive then
          List.for_all (is_really_smaller status r_uri r_len ~subst ~metasenv k) pl
        else
          let ty = typeof status ~subst ~metasenv context term in
          let dc_ctx, dcl, start, stop = 
            specialize_and_abstract_constrs status ~subst r_uri r_len context ty in
          List.for_all2
           (fun p (_,dc) -> 
             let rl = recursive_args status ~subst ~metasenv dc_ctx start stop dc in
             let e, k = get_new_safes status ~subst k p rl in
             is_really_smaller status r_uri r_len ~subst ~metasenv k e)
           pl dcl
    | _ -> List.for_all (is_really_smaller status r_uri r_len ~subst ~metasenv k) pl)
 | _ -> false

and returns_a_coinductive status ~subst context ty =
  match R.whd status ~subst context ty with
  | C.Const (Ref.Ref (uri,Ref.Ind (false,_,_)) as ref) 
  | C.Appl (C.Const (Ref.Ref (uri,Ref.Ind (false,_,_)) as ref)::_) ->
     let _, _, itl, _, _ = E.get_checked_indtys status ref in
     Some (uri,List.length itl)
  | C.Prod (n,so,de) ->
     returns_a_coinductive status ~subst ((n,C.Decl so)::context) de
  | _ -> None

and type_of_constant status ((Ref.Ref (uri,_)) as ref) = 
 let error () =
  raise (TypeCheckerFailure (lazy "Inconsistent cached infos in reference"))
 in
  match E.get_checked_obj status uri, ref with
  | (_,_,_,_,C.Inductive(isind1,lno1,tl,_)),Ref.Ref(_,Ref.Ind (isind2,i,lno2))->
      if isind1 <> isind2 || lno1 <> lno2 then error ();
      let _,_,arity,_ = List.nth tl i in arity
  | (_,_,_,_,C.Inductive (_,lno1,tl,_)), Ref.Ref (_,Ref.Con (i,j,lno2))  ->
      if lno1 <> lno2 then error ();
      let _,_,_,cl = List.nth tl i in 
      let _,_,arity = List.nth cl (j-1) in 
      arity
  | (_,_,_,_,C.Fixpoint (false,fl,_)), Ref.Ref (_,Ref.CoFix i) ->
      let _,_,_,arity,_ = List.nth fl i in
      arity
  | (_,h1,_,_,C.Fixpoint (true,fl,_)), Ref.Ref (_,Ref.Fix (i,recno2,h2)) ->
      let _,_,recno1,arity,_ = List.nth fl i in
      if h1 <> h2 || recno1 <> recno2 then error ();
      arity
  | (_,_,_,_,C.Constant (_,_,None,ty,_)), Ref.Ref (_,Ref.Decl) -> ty
  | (_,h1,_,_,C.Constant (_,_,Some _,ty,_)), Ref.Ref (_,Ref.Def h2) ->
     if h1 <> h2 then error ();
     ty
  | _ ->
    raise (AssertFailure
     (lazy ("type_of_constant: environment/reference: " ^
       Ref.string_of_reference ref)))

and get_relevance status ~metasenv ~subst context t args = 
   let ty = typeof status ~subst ~metasenv context t in
   let rec aux context ty = function
     | [] -> [] 
     | arg::tl -> match R.whd status ~subst context ty with
       | C.Prod (_,so,de) -> 
           let sort = typeof status ~subst ~metasenv context so in
           let new_ty = S.subst status ~avoid_beta_redexes:true arg de in
           (*prerr_endline ("so: " ^ status#ppterm ~subst ~metasenv:[]
             ~context so);
           prerr_endline ("sort: " ^ status#ppterm ~subst ~metasenv:[]
             ~context sort);*)
           (match R.whd status ~subst context sort with
              | C.Sort C.Prop ->
                  false::(aux context new_ty tl)
              | C.Sort _
              | C.Meta _ -> true::(aux context new_ty tl)
              | _ -> raise (TypeCheckerFailure (lazy (Printf.sprintf
                     "Prod: the type %s of the source of %s is not a sort" 
                      (status#ppterm ~subst ~metasenv ~context sort)
                      (status#ppterm ~subst ~metasenv ~context so)))))
       | _ ->
          raise 
            (TypeCheckerFailure
              (lazy (Printf.sprintf
                "Appl: %s is not a function, it cannot be applied"
                (status#ppterm ~subst ~metasenv ~context
                 (let res = List.length tl in
                  let eaten = List.length args - res in
                   (C.Appl
                    (t::fst
                     (HExtlib.split_nth eaten args))))))))
   in aux context ty args
;;

let typecheck_context status ~metasenv ~subst context =
 ignore
  (List.fold_right
   (fun d context  ->
     begin
      match d with
         _,C.Decl t -> ignore (typeof status ~metasenv ~subst:[] context t)
       | name,C.Def (te,ty) ->
         ignore (typeof status ~metasenv ~subst:[] context ty);
         let ty' = typeof status ~metasenv ~subst:[] context te in
          if not (R.are_convertible status ~metasenv ~subst context ty' ty) then
           raise (AssertFailure (lazy (Printf.sprintf (
            "the type of the definiens for %s in the context is not "^^
            "convertible with the declared one.\n"^^
            "inferred type:\n%s\nexpected type:\n%s")
            name (status#ppterm ~subst ~metasenv ~context ty') 
            (status#ppterm ~subst ~metasenv ~context ty))))
     end;
     d::context
   ) context [])
;;

let typecheck_metasenv status metasenv =
 ignore
  (List.fold_left
    (fun metasenv (i,(_,context,ty) as conj) ->
      if List.mem_assoc i metasenv then
       raise (TypeCheckerFailure (lazy ("duplicate meta " ^ string_of_int i ^
        " in metasenv")));
      typecheck_context status ~metasenv ~subst:[] context;
      ignore (typeof status ~metasenv ~subst:[] context ty);
      metasenv @ [conj]
    ) [] metasenv)
;;

let typecheck_subst status ~metasenv subst =
 ignore
  (List.fold_left
    (fun subst (i,(_,context,ty,bo) as conj) ->
      if List.mem_assoc i subst then
       raise (AssertFailure (lazy ("duplicate meta " ^ string_of_int i ^
        " in substitution")));
      if List.mem_assoc i metasenv then
       raise (AssertFailure (lazy ("meta " ^ string_of_int i ^
        " is both in the metasenv and in the substitution")));
      typecheck_context status ~metasenv ~subst context;
      ignore (typeof status ~metasenv ~subst context ty);
      let ty' = typeof status ~metasenv ~subst context bo in
       if not (R.are_convertible status ~metasenv ~subst context ty' ty) then
        raise (AssertFailure (lazy (Printf.sprintf (
         "the type of the definiens for %d in the substitution is not "^^
         "convertible with the declared one.\n"^^
         "inferred type:\n%s\nexpected type:\n%s")
         i
         (status#ppterm ~subst ~metasenv ~context ty') 
         (status#ppterm ~subst ~metasenv ~context ty))));
      subst @ [conj]
    ) [] subst)
;;

let height_of_term status tl =
 let h = ref 0 in
 let get_height (NReference.Ref (uri,_)) =
  let _,height,_,_,_ = NCicEnvironment.get_checked_obj status uri in
   height in
 let rec aux =
  function
     NCic.Meta (_,(_,NCic.Ctx l)) -> List.iter aux l
   | NCic.Meta _ -> ()
   | NCic.Rel _
   | NCic.Sort _ -> ()
   | NCic.Implicit _ -> assert false
   | NCic.Const nref -> h := max !h (get_height nref)
   | NCic.Prod (_,t1,t2)
   | NCic.Lambda (_,t1,t2) -> aux t1; aux t2
   | NCic.LetIn (_,s,ty,t) -> aux s; aux ty; aux t
   | NCic.Appl l -> List.iter aux l
   | NCic.Match (_,outty,t,pl) -> aux outty; aux t; List.iter aux pl
 in
  List.iter aux tl;
  1 + !h
;;

let height_of_obj_kind status uri ~subst =
 function
    NCic.Inductive _
  | NCic.Constant (_,_,None,_,_)
  | NCic.Fixpoint (false,_,_) -> 0
  | NCic.Fixpoint (true,ifl,_) ->
     let iflno = List.length ifl in
      height_of_term status
       (List.fold_left
        (fun l (_,_,_,ty,bo) ->
          let bo = debruijn status uri iflno [] ~subst bo in
           ty::bo::l
       ) [] ifl)
  | NCic.Constant (_,_,Some bo,ty,_) -> height_of_term status [bo;ty]
;;

let typecheck_obj status (uri,height,metasenv,subst,kind) =
(*height must be checked since it is not only an optimization during reduction*)
 let iheight = height_of_obj_kind status uri ~subst kind in
 if height <> iheight then
  raise (TypeCheckerFailure (lazy (Printf.sprintf
   "the declared object height (%d) is not the inferred one (%d)"
   height iheight)));
 typecheck_metasenv status metasenv;
 typecheck_subst status ~metasenv subst;
 match kind with
   | C.Constant (relevance,_,Some te,ty,_) ->
      benchmark (fun () ->
      let _ = typeof status ~subst ~metasenv [] ty in
      let ty_te = typeof status ~subst ~metasenv [] te in
      if not (R.are_convertible status ~metasenv ~subst [] ty_te ty) then
       raise (TypeCheckerFailure (lazy (Printf.sprintf (
        "the type of the body is not convertible with the declared one.\n"^^
        "inferred type:\n%s\nexpected type:\n%s")
        (status#ppterm ~subst ~metasenv ~context:[] ty_te) 
        (status#ppterm ~subst ~metasenv ~context:[] ty))));
      check_relevance status ~subst ~metasenv [] relevance ty;
      ) (fun () ->
      (*check_relevance status ~in_type:false ~subst ~metasenv relevance te*)
(* FG: extension for ELPI *)
      let r = Ref.reference_of_spec uri (Ref.Def height) in
      log (LP.has_type r te ty)
      )
(* FG: end of extension for ELPI *)
   | C.Constant (relevance,_,None,ty,_) ->
      benchmark (fun () ->
      ignore (typeof status ~subst ~metasenv [] ty);
      check_relevance status ~subst ~metasenv [] relevance ty;
      ) (fun () ->
(* FG: extension for ELPI *)
      let r = Ref.reference_of_spec uri Ref.Decl in
      log (LP.is_type r ty)
      )
(* FG: end of extension for ELPI *)
   | C.Inductive (_, leftno, tyl, _) -> 
       check_mutual_inductive_defs status uri ~metasenv ~subst leftno tyl
   | C.Fixpoint (inductive,fl,_) ->
      let types, kl =
        List.fold_left
         (fun (types,kl) (relevance,name,k,ty,_) ->
           let _ = typeof status ~subst ~metasenv [] ty in
            check_relevance status ~subst ~metasenv [] relevance ty;
            ((name,C.Decl ty)::types, k::kl)
         ) ([],[]) fl
      in
      let len = List.length types in
      let dfl, kl =   
        List.split (List.map2 
          (fun (_,_,_,_,bo) rno -> 
             let dbo = debruijn status uri len [] ~subst bo in
             dbo, Evil rno)
          fl kl)
      in
      List.iter2 (fun (_,_,x,ty,_) bo ->
       let ty_bo = typeof status ~subst ~metasenv types bo in
       if not (R.are_convertible status ~metasenv ~subst types ty_bo ty)
       then raise (TypeCheckerFailure (lazy ("(Co)Fix: ill-typed bodies")))
       else
        if inductive then begin
          let m, context = eat_lambdas status ~subst ~metasenv types (x + 1) bo in
          let r_uri, r_len =
            let he =
             match List.hd context with _,C.Decl t -> t | _ -> assert false
            in
            match R.whd status ~subst (List.tl context) he with
            | C.Const (Ref.Ref (uri,Ref.Ind _) as ref)
            | C.Appl (C.Const (Ref.Ref (uri,Ref.Ind _) as ref) :: _) ->
                let _,_,itl,_,_ = E.get_checked_indtys status ref in
                  uri, List.length itl
            | _ ->
              raise (TypeCheckerFailure
               (lazy "Fix: the recursive argument is not inductive"))
          in
          (* guarded by destructors conditions D{f,k,x,M} *)
          let rec enum_from k = 
            function [] -> [] | v::tl -> (k,v)::enum_from (k+1) tl 
          in
          guarded_by_destructors status r_uri r_len 
           ~subst ~metasenv context (enum_from (x+2) kl) m
        end else
         match returns_a_coinductive status ~subst [] ty with
          | None ->
             raise (TypeCheckerFailure
               (lazy "CoFix: does not return a coinductive type"))
          | Some (r_uri, r_len) ->
             (* guarded by constructors conditions C{f,M} *)
             if not 
             (guarded_by_constructors status ~subst ~metasenv types bo r_uri r_len len)
             then
               raise (TypeCheckerFailure
                (lazy ("CoFix: not guarded by constructors: " ^ status#ppobj (uri,height,metasenv,subst,kind))))
        ) fl dfl
;;

(* trust *)

let trust = ref  (fun _ -> false);;
let set_trust f = trust := f
let trust_obj obj = !trust obj


(* web interface stuff *)

let logger = 
 ref (function (`Start_type_checking _|`Type_checking_completed _|`Type_checking_interrupted _|`Type_checking_failed _|`Trust_obj _) -> ())
;;

let set_logger f = logger := f;;

let typecheck_obj status obj =
 let u,_,_,_,_ = obj in
 try
  !logger (`Start_type_checking u);
  typecheck_obj status obj;
  !logger (`Type_checking_completed u)
 with
    Sys.Break as e ->
     !logger (`Type_checking_interrupted u);
     raise e
  | e ->
     !logger (`Type_checking_failed u);
     raise e
;;

E.set_typecheck_obj
 (fun status obj ->
   if trust_obj obj then
    let u,_,_,_,_ = obj in
     !logger (`Trust_obj u)
   else
    typecheck_obj status obj)
;;

let _ = NCicReduction.set_get_relevance get_relevance;;

let indent = ref 0;;
let debug = true;;
let logger =
    let do_indent () = String.make !indent ' ' in  
    (function 
      | `Start_type_checking s ->
          if debug then
           prerr_endline (do_indent () ^ "Start: " ^ NUri.string_of_uri s); 
          incr indent
      | `Type_checking_completed s ->
          decr indent;
          if debug then
           prerr_endline (do_indent () ^ "End: " ^ NUri.string_of_uri s)
      | `Type_checking_interrupted s ->
          decr indent;
          if debug then
           prerr_endline (do_indent () ^ "Break: " ^ NUri.string_of_uri s)
      | `Type_checking_failed s ->
          decr indent;
          if debug then
           prerr_endline (do_indent () ^ "Fail: " ^ NUri.string_of_uri s)
      | `Trust_obj s ->
          if debug then
           prerr_endline (do_indent () ^ "Trust: " ^ NUri.string_of_uri s))
;;
(* let _ = set_logger logger ;; *)
(* EOF *)
