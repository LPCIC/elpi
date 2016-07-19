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

(* $Id: nCicUntrusted.ml 12809 2014-03-04 11:56:12Z sacerdot $ *)

module C = NCic
module Ref = NReference

let map_term_fold_a status g k f a = function
 | C.Meta _ -> assert false
 | C.Implicit _
 | C.Sort _
 | C.Const _
 | C.Rel _ as t -> a,t
 | C.Appl [] | C.Appl [_] -> assert false
 | C.Appl l as orig ->
    let fire_beta, upto = 
      match l with C.Meta _ :: _ -> true, List.length l - 1 | _ -> false, 0 
    in
    let a,l1 = HExtlib.sharing_map_acc (f k) a l in
    a, if l1 == l then orig else 
       let t =
        match l1 with
         | C.Appl l :: tl -> C.Appl (l@tl)
         | _ -> C.Appl l1
       in
        if fire_beta then NCicReduction.head_beta_reduce status ~upto t
        else t
 | C.Prod (n,s,t) as orig ->
     let a,s1 = f k a s in let a,t1 = f (g (n,C.Decl s) k) a t in
     a, if t1 == t && s1 == s then orig else C.Prod (n,s1,t1)
 | C.Lambda (n,s,t) as orig -> 
     let a,s1 = f k a s in let a,t1 = f (g (n,C.Decl s) k) a t in
     a, if t1 == t && s1 == s then orig else C.Lambda (n,s1,t1)
 | C.LetIn (n,ty,t,b) as orig -> 
     let a,ty1 = f k a ty in let a,t1 = f k a t in
     let a,b1 = f (g (n,C.Def (t,ty)) k) a b in
     a, if ty1 == ty && t1 == t && b1 == b then orig else C.LetIn (n,ty1,t1,b1)
 | C.Match (r,oty,t,pl) as orig -> 
     let a,oty1 = f k a oty in let a,t1 = f k a t in 
     let a,pl1 = HExtlib.sharing_map_acc (f k) a pl in
     a, if oty1 == oty && t1 == t && pl1 == pl then orig 
        else C.Match(r,oty1,t1,pl1)
;;

let metas_of_term status subst context term =
  let rec aux ctx acc = function
    | NCic.Rel i -> 
         (match HExtlib.list_skip (i-1) ctx with
         | (_,NCic.Def (bo,_)) :: ctx -> aux ctx acc bo
         | _ -> acc)
    | NCic.Meta(i,l) -> 
         (try
           let _,_,bo,_ = NCicUtils.lookup_subst i subst in
           let bo = NCicSubstitution.subst_meta status l bo in
           aux ctx acc bo
         with NCicUtils.Subst_not_found _ -> 
            let shift, lc = l in
            let lc = NCicUtils.expand_local_context lc in
            let l = List.map (NCicSubstitution.lift status shift) lc in
            List.fold_left (aux ctx) (i::acc) l)
    | t -> NCicUtils.fold (fun e c -> e::c) ctx aux acc t
  in
    HExtlib.list_uniq (List.sort Pervasives.compare (aux context [] term))
;;

module NCicHash =
 Hashtbl.Make
  (struct
    type t = C.term
    let equal = (==)
    let hash = Hashtbl.hash_param 100 1000 
   end)
;;

let mk_appl he args = 
  if args = [] then he else
  match he with
  | NCic.Appl l -> NCic.Appl (l@args)
  | _ -> NCic.Appl (he::args)
;;

let map_obj_kind ?(skip_body=false) f =
 let do_bo f x = if skip_body then x else f x in
 function
    NCic.Constant (relev,name,bo,ty,attrs) ->
     NCic.Constant (relev,name,do_bo (HExtlib.map_option f) bo, f ty,attrs)
  | NCic.Fixpoint (ind,fl,attrs) ->
     let fl =
      List.map
       (function (relevance,name,recno,ty,bo) -> 
          relevance,name,recno,f ty,do_bo f bo)
       fl
     in
      NCic.Fixpoint (ind,fl,attrs)
  | NCic.Inductive (is_ind,lno,itl,attrs) ->
      let itl = 
        List.map
         (fun (relevance,name,ty,cl) ->
           let cl = 
             List.map (fun (relevance, name, ty) ->
                relevance, name, f ty)
             cl
           in
           relevance, name, f ty, cl)
         itl
      in
      NCic.Inductive (is_ind,lno,itl,attrs)
;;

exception Occurr;;

let clean_or_fix_dependent_abstrations status ctx t =
  let occurrs_1 t =
    let rec aux n _ = function
      | NCic.Meta _ -> ()
      | NCic.Rel i when i = n + 1 -> raise Occurr
      | t -> NCicUtils.fold (fun _ k -> k + 1) n aux () t
    in
    try aux 0 () t; false
    with Occurr -> true
  in
  let fresh ctx name = 
    if not (List.mem name ctx) then name 
    else
     let rec aux i =
       let attempt = name ^ string_of_int i in
       if List.mem attempt ctx then aux (i+1) 
       else attempt
     in 
      aux 0
  in
  let rec aux ctx = function
  | NCic.Meta _ as t -> t
  | NCic.Prod (name,s,t) when name.[0] = '#' && occurrs_1 t ->
      let name = fresh ctx (String.sub name 1 (String.length name-1)) in
      NCic.Prod (name,aux ctx s, aux (name::ctx) t)
  | NCic.Prod (name,s,t) when name.[0] = '#' && not (occurrs_1 t) ->
      NCic.Prod ("_",aux ctx s,aux ("_"::ctx) t)
  | NCic.Prod ("_",s,t) -> NCic.Prod("_",aux ctx s,aux ("_"::ctx) t)
  | NCic.Prod (name,s,t) when name.[0] <> '_' && not (occurrs_1 t) ->
      let name = fresh ctx ("_"^name) in
      NCic.Prod (name, aux ctx s, aux (name::ctx) t)
  | NCic.Prod (name,s,t) when List.mem name ctx ->
      let name = fresh ctx name in
      NCic.Prod (name, aux ctx s, aux (name::ctx) t)
  | NCic.Lambda (name,s,t) when List.mem name ctx ->
      let name = fresh ctx name in
      NCic.Lambda (name, aux ctx s, aux (name::ctx) t)
  | t -> NCicUtils.map status (fun (e,_) ctx -> e::ctx) ctx aux t
  in
    aux (List.map fst ctx) t
;;

let rec fire_projection_redex status () = function
  | C.Meta _ as t -> t
  | C.Appl((C.Const(Ref.Ref(_,Ref.Fix(fno,rno,_)) as r) as hd)::args) as ot->
      let args'= HExtlib.sharing_map (fire_projection_redex status ()) args in
      let t = if args == args' then ot else C.Appl (hd::args') in
      let ifl,(_,_,pragma),_ = NCicEnvironment.get_checked_fixes_or_cofixes status r in
      if pragma <> `Projection || List.length args <= rno then t
      else
        (match List.nth args' rno with
        | C.Appl (C.Const(Ref.Ref(_,Ref.Con _))::_) ->
            let _, _, _, _, fbody = List.nth ifl fno in (* fbody is closed! *)
            let t = C.Appl (fbody::args') in
            (match NCicReduction.head_beta_reduce status ~delta:max_int t with
             | C.Match (_,_, C.Appl(C.Const(Ref.Ref(_,Ref.Con (_,_,leftno)))
                ::kargs),[pat])->
                  let _,kargs = HExtlib.split_nth leftno kargs in
                   NCicReduction.head_beta_reduce status
                    ~delta:max_int (C.Appl (pat :: kargs))
            | C.Appl(C.Match(_,_,C.Appl(C.Const(Ref.Ref(_,Ref.Con (_,_,leftno)))
               ::kargs),[pat]) :: args) ->
                  let _,kargs = HExtlib.split_nth leftno kargs in
                   fire_projection_redex status ()
                    (NCicReduction.head_beta_reduce status 
                      ~delta:max_int (C.Appl (pat :: kargs @ args)))
            | _ -> assert false) 
        | _ -> t)
  | t ->
     NCicUtils.map status (fun _ x -> x) () (fire_projection_redex status) t
;;

let apply_subst status ?(fix_projections=false) subst context t = 
 let rec apply_subst subst () =
 function
    NCic.Meta (i,lc) ->
     (try
       let _,_,t,_ = NCicUtils.lookup_subst i subst in
       let t = NCicSubstitution.subst_meta status lc t in
        apply_subst subst () t
      with
       NCicUtils.Subst_not_found j when j = i ->
        match lc with
           _,NCic.Irl _ -> NCic.Meta (i,lc)
         | n,NCic.Ctx l ->
            NCic.Meta
             (i,(0,NCic.Ctx
                 (List.map (fun t ->
                   apply_subst subst () (NCicSubstitution.lift status n t)) l))))
  | t -> NCicUtils.map status (fun _ () -> ()) () (apply_subst subst) t
 in
  let t = apply_subst subst () t in
  let t = clean_or_fix_dependent_abstrations status context t in
  if fix_projections then
   fire_projection_redex status () t
  else
   t
;;

let apply_subst_context status ~fix_projections subst context =
  let apply_subst = apply_subst status ~fix_projections in
  let rec aux c = function 
    | [] -> []
    | (name,NCic.Decl t as e) :: tl -> 
        (name, NCic.Decl (apply_subst subst c t)) :: aux (e::c) tl
    | (name,NCic.Def (t1,t2) as e) :: tl -> 
        (name, NCic.Def (apply_subst subst c t1,apply_subst subst c t2)) :: 
          aux (e::c) tl
  in
    List.rev (aux [] (List.rev context))
;;

let rec apply_subst_metasenv status subst = function
  | [] -> []
  | (i,_) :: _ when List.mem_assoc i subst -> assert false
  | (i,(name,ctx,ty)) :: tl ->
      (i,(name,apply_subst_context status ~fix_projections:true subst ctx,
               apply_subst status ~fix_projections:true subst ctx ty)) ::
         apply_subst_metasenv status subst tl
;;

(* hide optional arg *)
let apply_subst status s c t = apply_subst status s c t;;


type meta_kind = [ `IsSort | `IsType | `IsTerm ]

let is_kind x = x = `IsSort || x = `IsType || x = `IsTerm ;;

let kind_of_meta l =
  try 
    (match List.find is_kind l with
    | `IsSort | `IsType | `IsTerm as x -> x
    | _ -> assert false)
  with 
   Not_found -> assert false
;;

let rec replace_in_metasenv i f = function
  | [] -> assert false
  | (j,e)::tl when j=i -> (i,f e) :: tl
  | x::tl -> x :: replace_in_metasenv i f tl
;;
          
let rec replace_in_subst i f = function
  | [] -> assert false
  | (j,e)::tl when j=i -> (i,f e) :: tl
  | x::tl -> x :: replace_in_subst i f tl
;;
          
let set_kind newkind attrs = 
  (newkind :> NCic.meta_attr) :: List.filter (fun x -> not (is_kind x)) attrs 
;;

let max_kind k1 k2 = 
  match k1, k2 with
  | `IsSort, _ | _, `IsSort -> `IsSort
  | `IsType, _ | _, `IsType -> `IsType
  | _ -> `IsTerm
;;

module OT = 
  struct 
    type t = int * NCic.conjecture
    let compare (i,_) (j,_) = Pervasives.compare i j
  end

module MS = HTopoSort.Make(OT)
let relations_of_menv status subst m c =
  let i, (_, ctx, ty) = c in
  let m = List.filter (fun (j,_) -> j <> i) m in
  let m_ty = metas_of_term status subst ctx ty in
  let m_ctx =
   snd 
    (List.fold_right
     (fun i (ctx,res) ->
      (i::ctx),
      (match i with
       | _,NCic.Decl ty -> metas_of_term status subst ctx ty
       | _,NCic.Def (t,ty) -> 
         metas_of_term status subst ctx ty @ metas_of_term status subst ctx t) @ res)
    ctx ([],[]))
  in
  let metas = HExtlib.list_uniq (List.sort compare (m_ty @ m_ctx)) in
  List.filter (fun (i,_) -> List.exists ((=) i) metas) m
;;

let sort_metasenv status subst (m : NCic.metasenv) =
  (MS.topological_sort m (relations_of_menv status subst m) : NCic.metasenv)
;;

let count_occurrences status ~subst n t = 
  let occurrences = ref 0 in
  let rec aux k _ = function
    | C.Rel m when m = n+k -> incr occurrences
    | C.Rel _m -> ()
    | C.Implicit _ -> ()
    | C.Meta (_,(_,(C.Irl 0 | C.Ctx []))) -> (* closed meta *) ()
    | C.Meta (mno,(s,l)) ->
         (try
            (* possible optimization here: try does_not_occur on l and
               perform substitution only if DoesOccur is raised *)
            let _,_,term,_ = NCicUtils.lookup_subst mno subst in
            aux (k-s) () (NCicSubstitution.subst_meta status (0,l) term)
          with NCicUtils.Subst_not_found _ -> () (*match l with
          | C.Irl len -> if not (n+k >= s+len || s > nn+k) then raise DoesOccur
          | C.Ctx lc -> List.iter (aux (k-s) ()) lc*))
    | t -> NCicUtils.fold (fun _ k -> k + 1) k aux () t
  in
   aux 0 () t;
   !occurrences
;;

exception Found_variable

let looks_closed t = 
  let rec aux k _ = function
    | C.Rel m when k < m -> raise Found_variable
    | C.Rel _m -> ()
    | C.Implicit _ -> ()
    | C.Meta (_,(_,(C.Irl 0 | C.Ctx []))) -> (* closed meta *) ()
    | C.Meta _ -> raise Found_variable
    | t -> NCicUtils.fold (fun _ k -> k + 1) k aux () t
  in
  try aux 0 () t; true with Found_variable -> false
;;
