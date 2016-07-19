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

(* $Id: nCicReduction.ml 11296 2011-06-01 11:27:34Z sacerdot $ *)

module C = NCic
module Ref = NReference
module E = NCicEnvironment

exception AssertFailure of string Lazy.t;;

let debug = ref false;;
let pp m = if !debug then prerr_endline (Lazy.force m) else ();;

module type Strategy = sig
  type stack_term
  type env_term
  type config = int * env_term list * C.term * stack_term list
  val to_env :
   reduce: (delta:int -> config -> config * bool) -> 
   unwind: (config -> C.term) ->
    config -> env_term
  val from_stack : delta:int -> stack_term -> config
  val from_stack_list_for_unwind :
    unwind: (config -> C.term) -> stack_term list -> C.term list
  val from_env : delta:int -> env_term -> config
  val from_env_for_unwind :
    unwind: (config -> C.term) -> env_term -> C.term
  val stack_to_env :
   reduce: (delta:int -> config -> config * bool) -> 
   unwind: (config -> C.term) ->
    stack_term -> env_term
  val compute_to_env :
   reduce: (delta:int -> config -> config * bool) -> 
   unwind: (config -> C.term) ->
    int -> env_term list -> C.term -> env_term
  val compute_to_stack :
   reduce: (delta:int -> config -> config * bool) -> 
   unwind: (config -> C.term) ->
    config -> stack_term
 end
;;

module CallByValueByNameForUnwind' : Strategy = struct
  type config = int * env_term list * C.term * stack_term list
  and stack_term = 
       config Lazy.t * (int -> config) * C.term Lazy.t
  and env_term = 
        config Lazy.t    (* cbneed   ~delta:0       *)
      * (int -> config)  (* cbvalue  ~delta         *)
      * C.term Lazy.t    (* cbname   ~delta:max_int *)
  let to_env ~reduce ~unwind c = 
   lazy (fst (reduce ~delta:0 c)), 
   (fun delta -> fst (reduce ~delta c)),
   lazy (unwind c)
  let from_stack ~delta (c0,c,_) = if delta = 0 then Lazy.force c0 else c delta
  let from_stack_list_for_unwind ~unwind:_ l = 
   List.map (fun (_,_,c) -> Lazy.force c) l
  let from_env ~delta (c0,c,_) = if delta = 0 then Lazy.force c0 else c delta
  let from_env_for_unwind ~unwind:_ (_,_,c) = Lazy.force c
  let stack_to_env ~reduce:_ ~unwind:_ config = config
  let compute_to_env ~reduce ~unwind k e t =
   lazy (fst (reduce ~delta:0 (k,e,t,[]))), 
   (fun delta -> fst (reduce ~delta (k,e,t,[]))), 
   lazy (unwind (k,e,t,[]))
  let compute_to_stack ~reduce ~unwind config = 
   lazy (fst (reduce ~delta:0 config)), 
   (fun delta -> fst (reduce ~delta config)), 
   lazy (unwind config)
 end
;;

module Reduction(RS : Strategy) = struct
  type env = RS.env_term list
  type stack = RS.stack_term list
  type config = int * env * C.term * stack

  let rec unwind status (k,e,t,s) =
    let t = 
      if k = 0 then t 
      else 
        NCicSubstitution.psubst status ~avoid_beta_redexes:true
          (RS.from_env_for_unwind ~unwind:(unwind status)) e t
    in
    if s = [] then t 
    else C.Appl(t::(RS.from_stack_list_for_unwind ~unwind:(unwind status) s))
  ;;

  let list_nth l n = try List.nth l n with Failure _ -> assert false;;
  let rec replace i s t =
    match i,s with
    |  0,_::tl -> t::tl
    | n,he::tl -> he::(replace (n - 1) tl t)
    | _,_ -> assert false
  ;;

  let rec reduce status ~delta ?(subst = []) context : config -> config * bool =
   let rec aux = function
     | k, e, C.Rel n, s when n <= k ->
        let k',e',t',s' = RS.from_env ~delta (list_nth e (n-1)) in
        aux (k',e',t',s'@s)
     | k, _, C.Rel n, s as config (* when n > k *) ->
        let x= try Some (List.nth context (n - 1 - k)) with Failure _ -> None in
         (match x with
         | Some(_,C.Def(x,_)) -> aux (0,[],NCicSubstitution.lift status (n - k) x,s)
         | _ -> config, true)
     | (k, e, C.Meta (n,l), s) as config ->
        (try 
           let _,_, term,_ = NCicUtils.lookup_subst n subst in
           aux (k, e, NCicSubstitution.subst_meta status l term,s)
         with  NCicUtils.Subst_not_found _ -> config, true)
     | (_, _, C.Implicit _, _) -> assert false
     | (_, _, C.Sort _, _)
     | (_, _, C.Prod _, _)
     | (_, _, C.Lambda _, []) as config -> config, true
     | (k, e, C.Lambda (_,_,t), p::s) ->
         aux (k+1, (RS.stack_to_env ~reduce:(reduce status ~subst context) ~unwind:(unwind status) p)::e, t,s)
     | (k, e, C.LetIn (_,_,m,t), s) ->
        let m' = RS.compute_to_env ~reduce:(reduce status ~subst context) ~unwind:(unwind status) k e m in
         aux (k+1, m'::e, t, s)
     | (_, _, C.Appl ([]|[_]), _) -> assert false
     | (k, e, C.Appl (he::tl), s) ->
        let tl' =
         List.map (fun t->RS.compute_to_stack 
           ~reduce:(reduce status ~subst context) ~unwind:(unwind status) (k,e,t,[])) tl
        in
         aux (k, e, he, tl' @ s)
     | (_, _, C.Const
            (Ref.Ref (_,Ref.Def height) as refer), s) as config ->
         if delta >= height then 
           config, false
         else 
           let _,_,body,_,_,_ = NCicEnvironment.get_checked_def status refer in
           aux (0, [], body, s) 
     | (_, _, C.Const (Ref.Ref (_,
         (Ref.Decl|Ref.Ind _|Ref.Con _|Ref.CoFix _))), _) as config -> 
           config, true
     | (_, _, (C.Const (Ref.Ref 
          (_,Ref.Fix (fixno,recindex,height)) as refer)),s) as config ->
        (let arg = try Some (List.nth s recindex) with Failure _ -> None in
         match arg with
            None -> config, true
          | Some arg ->
             let fixes,(_,_,pragma),_ = 
              NCicEnvironment.get_checked_fixes_or_cofixes status refer in
             if delta >= height then
              match pragma with
               | `Projection ->
                   (match RS.from_stack ~delta:max_int arg with
                     | _,_,C.Const(Ref.Ref(_,Ref.Con _)),_::_ ->
                       let _,_,_,_,body = List.nth fixes fixno in
                        aux (0, [], body, s)
                     | _ -> config,false)
               | _ -> config,false
             else
              match RS.from_stack ~delta:0 arg with
               | (_,_,C.Const (Ref.Ref (_,Ref.Con _)), _) as c ->
                 let new_s =
                  replace recindex s
                   (RS.compute_to_stack ~reduce:(reduce status ~subst context)
                   ~unwind:(unwind status) c) in
                 let _,_,_,_,body = List.nth fixes fixno in
                  aux (0, [], body, new_s)
               | _ -> config, true)
     | (k, e, C.Match (_,_,term,pl),s) as config ->
        let decofix = function
          | (_,_,C.Const(Ref.Ref(_,Ref.CoFix c)as refer),s)->
             let cofixes,_,_ = 
               NCicEnvironment.get_checked_fixes_or_cofixes status refer in
             let _,_,_,_,body = List.nth cofixes c in
             let c,_ = reduce status ~delta:0 ~subst context (0,[],body,s) in 
             c
          | config -> config
        in
        let match_head = k,e,term,[] in
        let reduced,_ = reduce status ~delta:0 ~subst context match_head in
        (match decofix reduced with
        | (_, _, C.Const (Ref.Ref (_,Ref.Con (_,j,_))),[]) ->
            aux (k, e, List.nth pl (j-1), s)
        | (_, _, C.Const (Ref.Ref (_,Ref.Con (_,j,lno))), s')->
          let _,params = HExtlib.split_nth lno s' in
          aux (k, e, List.nth pl (j-1), params@s)
        | _ -> config, true)
   in
    aux
  ;;

  let whd status ?(delta=0) ~subst context t = 
   unwind status (fst (reduce status ~delta ~subst context (0, [], t, [])))
  ;;

 end
;;


module RS = CallByValueByNameForUnwind';;
module R = Reduction(RS);;

let whd = R.whd

let (===) x y = Pervasives.compare x y = 0 ;;

let get_relevance = ref (fun _ ~metasenv:_ ~subst:_ _ _ -> assert false);;

let set_get_relevance = (:=) get_relevance;;

let alpha_eq (status:#NCic.status) ~test_lambda_source aux test_eq_only metasenv subst context
 t1 t2 =
 if t1 === t2 then
   true
 else
   match (t1,t2) with
   | C.Sort s1, C.Sort s2 -> 
       NCicEnvironment.are_sorts_convertible ~test_eq_only s1 s2 

   | (C.Prod (name1,s1,t1), C.Prod(_,s2,t2)) ->
       aux true context s1 s2 &&
       aux test_eq_only ((name1, C.Decl s1)::context) t1 t2
   | (C.Lambda (name1,s1,t1), C.Lambda(_,_,t2)) ->
      if test_lambda_source then
       aux test_eq_only context t1 t2
      else
       (* thanks to inversion of well typedness, the source 
        * of these lambdas must be already convertible *)
       aux test_eq_only ((name1, C.Decl s1)::context) t1 t2
   | (C.LetIn (name1,ty1,s1,t1), C.LetIn(_,ty2,s2,t2)) ->
      aux test_eq_only context ty1 ty2 &&
      aux test_eq_only context s1 s2 &&
      aux test_eq_only ((name1, C.Def (s1,ty1))::context) t1 t2

   | (C.Meta (n1,(s1, C.Irl _)), C.Meta (n2,(s2, C.Irl _))) 
      when n1 = n2 && s1 = s2 -> true
   | (C.Meta (n1,(s1, l1)), C.Meta (n2,(s2, l2))) when n1 = n2 &&
      let l1 = NCicUtils.expand_local_context l1 in
      let l2 = NCicUtils.expand_local_context l2 in
      (try List.for_all2 
        (fun t1 t2 -> aux test_eq_only context 
          (NCicSubstitution.lift status s1 t1) 
          (NCicSubstitution.lift status s2 t2))  
        l1 l2
      with Invalid_argument "List.for_all2" -> 
        prerr_endline ("Meta " ^ string_of_int n1 ^ 
          " occurrs with local contexts of different lenght\n"^
          status#ppterm ~metasenv ~subst ~context t1 ^ " === " ^
          status#ppterm ~metasenv ~subst ~context t2);
        assert false) -> true

   | C.Meta (n1,l1), _ ->
      (try 
         let _,_,term,_ = NCicUtils.lookup_subst n1 subst in
         let term = NCicSubstitution.subst_meta status l1 term in
          aux test_eq_only context term t2
       with NCicUtils.Subst_not_found _ -> false)
   | _, C.Meta (n2,l2) ->
      (try 
         let _,_,term,_ = NCicUtils.lookup_subst n2 subst in
         let term = NCicSubstitution.subst_meta status l2 term in
          aux test_eq_only context t1 term
       with NCicUtils.Subst_not_found _ -> false)
   
   | (C.Appl ((C.Const r1) as hd1::tl1), C.Appl (C.Const r2::tl2)) 
       when (Ref.eq r1 r2 && 
         List.length (E.get_relevance status r1) >= List.length tl1) ->
     let relevance = E.get_relevance status r1 in
(* if the types were convertible the following optimization is sound
     let relevance = match r1 with
         | Ref.Ref (_,Ref.Con (_,_,lno)) ->
             let _,relevance = HExtlib.split_nth lno relevance in
               HExtlib.mk_list false lno @ relevance
         | _ -> relevance
     in
*)
     (try
         HExtlib.list_forall_default3_var
          (fun t1 t2 b -> not b || aux true context t1 t2 )
          tl1 tl2 true relevance
        with Invalid_argument _ -> false
           | HExtlib.FailureAt fail ->
             let relevance = 
               !get_relevance (status :> NCic.status) ~metasenv ~subst context hd1 tl1 in
             let _,relevance = HExtlib.split_nth fail relevance in
             let b,relevance = (match relevance with
               | [] -> assert false
               | b::tl -> b,tl) in
             if (not b) then
               let _,tl1 = HExtlib.split_nth (fail+1) tl1 in
               let _,tl2 = HExtlib.split_nth (fail+1) tl2 in
                 try
                    HExtlib.list_forall_default3
                    (fun t1 t2 b -> not b || aux true context t1 t2)
                    tl1 tl2 true relevance
                 with Invalid_argument _ -> false
             else false)

   | (C.Appl (hd1::tl1),  C.Appl (hd2::tl2)) ->
       aux test_eq_only context hd1 hd2 &&
        let relevance = !get_relevance (status :> NCic.status) ~metasenv ~subst context hd1 tl1 in
        (try
         HExtlib.list_forall_default3
          (fun t1 t2 b -> not b || aux true context t1 t2)
          tl1 tl2 true relevance
        with Invalid_argument _ -> false)

   | (C.Match (Ref.Ref (_,Ref.Ind (_,tyno,_)) as ref1,outtype1,term1,pl1),
      C.Match (ref2,outtype2,term2,pl2)) ->
       let _,_,itl,_,_ = E.get_checked_indtys status ref1 in
       let _,_,ty,_ = List.nth itl tyno in
       let rec remove_prods ~subst context ty = 
         let ty = whd status ~subst context ty in
         match ty with
         | C.Sort _ -> ty
         | C.Prod (name,so,ta) -> remove_prods ~subst ((name,(C.Decl so))::context) ta
         | _ -> assert false
       in
       let is_prop = 
         match remove_prods ~subst [] ty with
         | C.Sort C.Prop -> true
         | _ -> false
       in
       Ref.eq ref1 ref2 &&
       aux test_eq_only context outtype1 outtype2 &&
       (is_prop || aux test_eq_only context term1 term2) &&
       (try List.for_all2 (aux test_eq_only context) pl1 pl2
        with Invalid_argument _ -> false)
   | (C.Implicit _, _) | (_, C.Implicit _) -> true
     (* CSC: was assert false, but it happens when looking for coercions
        during pretty printing of terms yet to be refined *)
   | (_,_) -> false
;;

(* t1, t2 must be well-typed *)
let are_convertible status ~metasenv ~subst =
 let rec aux test_eq_only context t1 t2 =
  let alpha_eq status test_eq_only =
   alpha_eq status ~test_lambda_source:false aux test_eq_only metasenv subst
    context
  in
   if alpha_eq status test_eq_only t1 t2 then 
     true
   else
     let height_of = function
      | C.Const (Ref.Ref (_,Ref.Def h)) 
      | C.Const (Ref.Ref (_,Ref.Fix (_,_,h))) 
      | C.Appl(C.Const(Ref.Ref(_,Ref.Def h))::_) 
      | C.Appl(C.Const(Ref.Ref(_,Ref.Fix (_,_,h)))::_) -> h
      | _ -> 0
     in
     let put_in_whd m1 m2 =
       R.reduce status ~delta:max_int ~subst context m1,
       R.reduce status ~delta:max_int ~subst context m2
     in
     let small_delta_step 
       ((_,_,t1,_ as m1), norm1 as x1) ((_,_,t2,_ as m2), norm2 as x2) 
     = 
       assert(not (norm1 && norm2));
       if norm1 then
         x1, R.reduce status ~delta:(height_of t2 -1) ~subst context m2
       else if norm2 then
         R.reduce status ~delta:(height_of t1 -1) ~subst context m1, x2
       else
        let h1 = height_of t1 in 
        let h2 = height_of t2 in
        let delta = if h1 = h2 then max 0 (h1 -1) else min h1 h2 in
        R.reduce status ~delta ~subst context m1,
        R.reduce status ~delta ~subst context m2
     in
     let rec convert_machines test_eq_only
       ((k1,e1,t1,s1),norm1 as m1),((k2,e2,t2,s2), norm2 as m2) 
     =
       (alpha_eq status test_eq_only
         (R.unwind status (k1,e1,t1,[])) (R.unwind status (k2,e2,t2,[])) &&
        let relevance =
          match t1 with
              C.Const r -> NCicEnvironment.get_relevance status r
            | _ -> [] in
        try
         HExtlib.list_forall_default3
           (fun t1 t2 b  ->
             not b ||
             let t1 = RS.from_stack ~delta:max_int t1 in
             let t2 = RS.from_stack ~delta:max_int t2 in
             convert_machines true (put_in_whd t1 t2)) s1 s2 true relevance
        with Invalid_argument _ -> false) || 
       (not (norm1 && norm2) && convert_machines test_eq_only (small_delta_step m1 m2))
     in
     convert_machines test_eq_only (put_in_whd (0,[],t1,[]) (0,[],t2,[]))
 in
  aux false 
;;

let alpha_eq status metasenv subst =
 let rec aux test_lambda_source context t1 t2 =
  alpha_eq status ~test_lambda_source aux true metasenv subst context t1 t2
 in
  aux true
;;

let rec head_beta_reduce status ~delta ~upto ~subst t l =
 match upto, t, l with
  | 0, C.Appl l1, _ -> C.Appl (l1 @ l)
  | 0, t, [] -> t
  | 0, t, _ -> C.Appl (t::l)
  | _, C.Meta (n,ctx), _ ->
     (try
       let _,_, term,_ = NCicUtils.lookup_subst n subst in
       head_beta_reduce status ~delta ~upto ~subst 
         (NCicSubstitution.subst_meta status ctx term) l
     with NCicUtils.Subst_not_found _ -> if l = [] then t else C.Appl (t::l))
  | _, C.Appl (hd::tl), _ -> head_beta_reduce status ~delta ~upto ~subst hd (tl @ l)
  | _, C.Lambda(_,_,bo), arg::tl ->
     let bo = NCicSubstitution.subst status arg bo in
     head_beta_reduce status ~delta ~upto:(upto - 1) ~subst bo tl
  | _, C.Const (Ref.Ref (_, Ref.Def height) as re), _ 
    when delta <= height ->
      let _, _, bo, _, _, _ = NCicEnvironment.get_checked_def status re in
      head_beta_reduce status ~upto ~delta ~subst bo l
  | _, t, [] -> t
  | _, t, _ -> C.Appl (t::l)
;;

let head_beta_reduce status ?(delta=max_int) ?(upto= -1) ?(subst=[]) t = 
  head_beta_reduce status ~delta ~upto ~subst t []
;;

type stack_item = RS.stack_term
type environment_item = RS.env_term

type machine = int * environment_item list * NCic.term * stack_item list

let reduce_machine = R.reduce
let from_stack = RS.from_stack
let from_env = RS.from_env
let unwind = R.unwind

let _ = 
  NCicUtils.set_head_beta_reduce
   (fun status ~upto t -> head_beta_reduce status ~upto t);
;;

(* if n < 0, then splits all prods from an arity, returning a sort *)
let rec split_prods status ~subst context n te =
  match (n, R.whd status ~subst context te) with
   | (0, _) -> context,te
   | (n, C.Sort _) when n <= 0 -> context,te
   | (n, C.Prod (name,so,ta)) ->
       split_prods status ~subst ((name,(C.Decl so))::context) (n - 1) ta
   | (_, _) -> raise (AssertFailure (lazy "split_prods"))
;;

(* vim:set foldmethod=marker: *)
