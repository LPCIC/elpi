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

(* let debug s = prerr_endline (Lazy.force s) ;;*)
let debug _ = ();;

let skel_dummy = NCic.Implicit `Type;;

let product f l1 l2 =
  List.fold_left
    (fun acc x ->
      List.fold_left 
        (fun acc y ->
           f x y :: acc)
        acc l2)
    [] l1  
;;

let pos_in_list x l =
      match 
        HExtlib.list_findopt (fun y i -> if y = x then Some i else None) l
      with
      | Some i -> i
      | None -> assert false
;;

let rec count_prod = function
  | NCic.Prod (_,_,x) -> 1 + count_prod x
  | _ -> 0
;;

let term_at i t =
  match t with
  | NCic.Appl l -> 
      (match 
        HExtlib.list_findopt (fun y j -> if i+1=j then Some y else None) l
      with
      | Some i -> i
      | None -> assert false)
  | _ -> assert false
;;

let rec cleanup_funclass_skel = function
    | NCic.Prod (_,_,t) -> 
        NCic.Prod ("_",skel_dummy, cleanup_funclass_skel t)
    | _ -> skel_dummy
;;

let src_tgt_of_ty_cpos_arity status ty cpos arity =
  let pis = count_prod ty in
  let tpos = pis - arity in
  let rec pi_nth i j = function
    | NCic.Prod (_,s,_) when i = j -> s
    | NCic.Prod (_,_,t) -> pi_nth (i+1) j t
    | t -> assert (i = j); t
  in
  let rec pi_tail i j = function
    | NCic.Prod (_,_,_) as t when i = j -> cleanup_funclass_skel t
    | NCic.Prod (_,_,t) -> pi_tail (i+1) j t
    | t -> assert (i = j); t
  in
  let mask t =
    let rec aux () = function
      | NCic.Meta _ 
      | NCic.Implicit _ as x -> x
      | NCic.Rel _ -> skel_dummy
      | t -> NCicUtils.map status (fun _ () -> ()) () aux t
    in
     aux () t
  in 
  mask (pi_nth 0 cpos ty), 
  mask (pi_tail 0 tpos ty)
;;

let rec cleanup_skel status () = function
  | NCic.Meta _ -> skel_dummy
  | t -> NCicUtils.map status (fun _ () -> ()) () (cleanup_skel status) t
;;

let close_in_context status t metasenv = 
  let rec aux m_subst subst ctx = function
   | (i,(tag,[],ty)) :: tl ->
        let name = "x" ^ string_of_int (List.length ctx) in
        let subst = (i,(tag,[],NCic.Rel (List.length tl+1),ty))::subst in
        let ty = NCicUntrusted.apply_subst status (m_subst (List.length ctx)) ctx ty in
        let m_subst m = 
          (i,(tag,[],NCic.Rel (m-List.length ctx),ty))::(m_subst m)
        in
        NCic.Lambda (name, ty, aux m_subst subst ((name,NCic.Decl ty)::ctx) tl)
   | [] -> 
           (* STRONG ASSUMPTION: 
                since metas occurring in t have an empty context,
                the substitution i build makes sense (i.e, the Rel
                I pun in the subst will not be lifted by subst_meta *)
           NCicUntrusted.apply_subst status subst ctx
             (NCicSubstitution.lift status (List.length ctx) t)
   | _ -> assert false
  in
  aux (fun _ -> []) [] [] metasenv
;;

let toposort status metasenv = 
  let module T = HTopoSort.Make(
    struct type t = int * NCic.conjecture let compare (i,_) (j,_) = i-j end) 
  in
  let deps (_,(_,_,t)) =
    List.filter (fun (j,_) -> 
      List.mem j (NCicUntrusted.metas_of_term status [] [] t)) metasenv
  in
  T.topological_sort metasenv deps
;;

let only_head = function
  | NCic.Appl (h::tl) -> 
      NCic.Appl (h :: HExtlib.mk_list skel_dummy (List.length tl))
  | t -> t
;;

let src_tgt_cpos_arity_of_ty_id_src_tgt status ty id src tgt =
  let status, src, cpos = 
    let rec aux cpos ctx = function
      | NCic.Prod (name,ty,bo) -> 
         if name <> id then aux (cpos+1) ((name,NCic.Decl ty)::ctx) bo
         else
           (try 
            let metasenv,subst,status,src =
              GrafiteDisambiguate.disambiguate_nterm 
                status `XTSort ctx [] [] ("",0,src) in
            let src = NCicUntrusted.apply_subst status subst [] src in
            (* CHECK that the declared pattern matches the abstraction *)
            let _ = NCicUnification.unify status metasenv subst ctx ty src in
            let src = cleanup_skel status () src in
            status, src, cpos
           with 
           | NCicUnification.UnificationFailure msg
           | NCicUnification.Uncertain msg ->
               raise (GrafiteTypes.Command_error ("bad source pattern: " ^ 
Lazy.force msg))
            | MultiPassDisambiguator.DisambiguationError _ ->
               raise (GrafiteTypes.Command_error ("bad source pattern: 
disambiguation error")))
      | _ -> assert false
    in
      aux 0 [] ty
  in
  let status, tgt, arity = 
    let metasenv,subst,status,tgt =
      GrafiteDisambiguate.disambiguate_nterm 
        status `XTSort [] [] [] ("",0,tgt) in
    let tgt = NCicUntrusted.apply_subst status subst [] tgt in
    (* CHECK che sia unificabile mancante *)
    let rec count_prod = function
      | NCic.Prod (_,_,x) -> 1 + count_prod x
      | _ -> 0
    in
    let arity = count_prod tgt in
    let tgt=
      if arity > 0 then cleanup_funclass_skel tgt 
      else cleanup_skel status () tgt 
    in
     status, tgt, arity
  in
  status, src, tgt, cpos, arity
;;

let fresh_uri status prefix suffix = 
  let mk x = NUri.uri_of_string (status#baseuri ^ "/" ^ prefix ^ x ^ suffix) in
  let rec diverge u i =
    if NCicLibrary.aliases_of u = [] then u
    else diverge (mk ("__" ^ string_of_int i)) (i+1)
  in
   diverge (mk "") 0
;;

exception Stop;;

let close_graph name t s d to_s from_d p a status =
  let c =
    List.find 
     (function (_,_,NCic.Appl (x::_),_,_) -> x = t | _ -> assert false) 
      (NCicCoercion.look_for_coercion status [] [] [] s d)
  in
  let compose_names a b = a ^ "__o__" ^ b in
  let composites = 
    let to_s_o_c = 
      product 
        (fun (n1,m1,t1,_,j) (n,mc,c,_,i) -> 
          compose_names n1 n,m1@mc,c,[i,t1],j,a) 
        to_s [c]
    in
    let c_o_from_d = 
      product 
        (fun (n,mc,c,_,j) (n1,m1,t1,ty,i) -> 
          compose_names n n1,m1@mc,t1,[i,c],j,count_prod ty) 
        [c] from_d
    in
    let to_s_o_c_o_from_d =
      product 
        (fun (n1,m1,t1,_,j) (n,m,t,upl,i,a)-> 
          compose_names n1 n,m@m1,t,(i,t1)::upl,j,a)
        to_s c_o_from_d
    in
    to_s_o_c @ c_o_from_d @ to_s_o_c_o_from_d
  in
  let composites =
    HExtlib.filter_map
     (fun (name,metasenv, bo, upl, p, arity) ->
        try
         let metasenv, subst = 
           List.fold_left 
            (fun (metasenv,subst) (a,b) ->
                NCicUnification.unify status metasenv subst [] a b)
            (metasenv,[]) upl
         in
         let bo = NCicUntrusted.apply_subst status subst [] bo in
         let p = NCicUntrusted.apply_subst status subst [] p in
         let metasenv = NCicUntrusted.apply_subst_metasenv status subst metasenv in
         let metasenv = toposort status metasenv in
         let bo = close_in_context status bo metasenv in
         let pos = 
           match p with 
           | NCic.Meta (p,_) -> pos_in_list p (List.map fst metasenv) 
           | t -> raise Stop
         in
         let ty = NCicTypeChecker.typeof status ~metasenv:[] ~subst:[] [] bo in
         let src,tgt = src_tgt_of_ty_cpos_arity status ty pos arity in
         let src = only_head src in
         let tgt = only_head tgt in
         debug (lazy(
           "composite " ^ name ^ ": "^
           status#ppterm ~metasenv:[] ~subst:[] ~context:[] bo ^ " : " ^
           status#ppterm ~metasenv:[] ~subst:[] ~context:[] ty ^ " as " ^
           status#ppterm ~metasenv:[] ~subst:[] ~context:[] src ^ " ===> " ^
           status#ppterm ~metasenv:[] ~subst:[] ~context:[] tgt ^
           " cpos=" ^ string_of_int pos ^ " arity=" ^ string_of_int arity));
         let uri = fresh_uri status name ".con" in
         let obj_kind = NCic.Constant 
           ([],name,Some bo,ty,(`Generated,`Definition,`Coercion arity)) 
         in
         let height = NCicTypeChecker.height_of_obj_kind status uri [] obj_kind in
         let obj = uri,height,[],[],obj_kind in
         let c = 
           NCic.Const 
             (NReference.reference_of_spec uri (NReference.Def height))
         in
         Some (obj,name,c,src,tgt,pos,arity)
       with 
       | NCicTypeChecker.TypeCheckerFailure _
       | NCicUnification.UnificationFailure _ 
       | NCicUnification.Uncertain _ | Stop -> None
     ) composites
  in
    composites
;;

(* idempotent *)
let basic_index_ncoercion (name,_compose,t,s,d,position,arity) status =
  NCicCoercion.index_coercion status name t s d arity position
;;

let basic_eval_ncoercion (name,compose,t,s,d,p,a) status =
  let to_s = 
    NCicCoercion.look_for_coercion status [] [] [] skel_dummy s
  in
  let from_d = 
    NCicCoercion.look_for_coercion status [] [] [] d skel_dummy
  in
  let status = NCicCoercion.index_coercion status name t s d a p in
  let composites =
   if compose then close_graph name t s d to_s from_d p a status else [] in
  List.fold_left 
    (fun (uris,infos,st) ((uri,_,_,_,_ as obj),name,t,s,d,p,a) -> 
      let info = name,compose,t,s,d,p,a in
      let st = NCicLibrary.add_obj st obj in
      let st = basic_index_ncoercion info st in
      uri::uris, info::infos, st)
    ([],[],status) composites
;;

let record_ncoercion =
 let aux (name,compose,t,s,d,p,a) ~refresh_uri_in_term =
  let t = refresh_uri_in_term t in
  let s = refresh_uri_in_term s in
  let d = refresh_uri_in_term d in
   basic_index_ncoercion (name,compose,t,s,d,p,a)
 in
 let aux_l l ~refresh_uri_in_universe ~refresh_uri_in_term
  ~refresh_uri_in_reference ~alias_only status
 =
  if not alias_only then
   List.fold_right (aux ~refresh_uri_in_term:(refresh_uri_in_term (status:>NCic.status))) l status
  else
   status
 in
  GrafiteTypes.Serializer.register#run "ncoercion" aux_l
;;

let basic_eval_and_record_ncoercion infos status =
 let uris, cinfos, status = basic_eval_ncoercion infos status in
  NCicLibrary.dump_obj status (record_ncoercion (infos::cinfos)), uris
;;

let basic_eval_and_record_ncoercion_from_t_cpos_arity 
      status (name,compose,t,cpos,arity) 
=
  let ty = NCicTypeChecker.typeof status ~subst:[] ~metasenv:[] [] t in
  let src,tgt = src_tgt_of_ty_cpos_arity status ty cpos arity in
  let status, uris =
   basic_eval_and_record_ncoercion (name,compose,t,src,tgt,cpos,arity) status
  in
   status,uris
;;

let eval_ncoercion (status: #GrafiteTypes.status) name compose t ty (id,src) tgt = 
 let metasenv,subst,status,ty =
  GrafiteDisambiguate.disambiguate_nterm status `XTSort [] [] [] ("",0,ty) in
 assert (metasenv=[]);
 let ty = NCicUntrusted.apply_subst status subst [] ty in
 let metasenv,subst,status,t =
  GrafiteDisambiguate.disambiguate_nterm status (`XTSome ty) [] [] [] ("",0,t) in
 assert (metasenv=[]);
 let t = NCicUntrusted.apply_subst status subst [] t in
 let status, src, tgt, cpos, arity = 
   src_tgt_cpos_arity_of_ty_id_src_tgt status ty id src tgt in
 let status, uris =
  basic_eval_and_record_ncoercion (name,compose,t,src,tgt,cpos,arity) status
 in
  status,uris
;;

