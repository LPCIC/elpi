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

(* $Id: orderings.ml 9869 2009-06-11 22:52:38Z denes $ *)

NCicBlob.set_default_eqP()
;;
NCicProof.set_default_sig()
;;

let noprint _ = ();;
let print s = prerr_endline (Lazy.force s);; 
let debug = noprint;; 

module B(C : NCicBlob.NCicContext): Orderings.Blob 
  with type t = NCic.term and type input = NCic.term 
  = Orderings.LPO(NCicBlob.NCicBlob(C))

module NCicParamod(C : NCicBlob.NCicContext) = Paramod.Paramod(B(C))

let readback status ?(demod=false) metasenv subst context (bag,i,fo_subst,l) =
(*
  List.iter (fun x ->
     print_endline (Pp.pp_unit_clause ~margin:max_int
     (fst(Terms.M.find x bag)))) l; 
*)
  (* let stamp = Unix.gettimeofday () in *)
  let proofterm,prooftype = NCicProof.mk_proof status ~demod bag i fo_subst l in
  (* debug (lazy (Printf.sprintf "Got proof term in %fs"
		     (Unix.gettimeofday() -. stamp))); *)
(*
  let metasenv, proofterm = 
    let rec aux k metasenv = function
      | NCic.Meta _ as t -> metasenv, t
      | NCic.Implicit _ -> 
          let metasenv, i, _, _ =
            NCicMetaSubst.mk_meta metasenv context `IsTerm 
          in
            metasenv, NCic.Meta (i,(k,NCic.Irl (List.length context)))
      | t -> NCicUntrusted.map_term_fold_a 
          (fun _ k -> k+1) k aux metasenv t
    in
      aux 0 metasenv proofterm
  in *)
  debug (lazy (status#ppterm ~metasenv ~subst ~context proofterm));
(*
  let stamp = Unix.gettimeofday () in
  let metasenv, subst, proofterm, _prooftype = 
    NCicRefiner.typeof 
      (status#set_coerc_db NCicCoercion.empty_db) 
      metasenv subst context proofterm None
  in
    print (lazy (Printf.sprintf "Refined in %fs"
		     (Unix.gettimeofday() -. stamp)));
*)
    proofterm, prooftype, metasenv, subst

let nparamod status metasenv subst context t table =
  let module C =
    struct 
      let metasenv = metasenv
      let subst = subst
      let context = context 
    end 
  in
  let module B = B(C) in
  let module P = NCicParamod(C) in
  let module Pp = Pp.Pp(B) in
  let bag, maxvar = Terms.empty_bag, 0 in
  let (bag,maxvar), goals = 
    HExtlib.list_mapi_acc (fun x _ a -> P.mk_goal a x) (bag,maxvar) [t]
  in
  let (bag,maxvar), passives = 
    HExtlib.list_mapi_acc (fun x _ a -> P.mk_passive a x) (bag,maxvar) table
  in
  match 
    P.paramod ~useage:true ~max_steps:max_int ~timeout:(Unix.gettimeofday () +. 300.0) 
      ~g_passives:goals ~passives (bag,maxvar) 
  with 
  | P.Error _ | P.GaveUp | P.Timeout _ -> []
  | P.Unsatisfiable solutions -> 
      List.map (readback status metasenv subst context) solutions
;;
  
module EmptyC = 
  struct
    let metasenv = []
    let subst = []
    let context = []
  end

module CB = NCicBlob.NCicBlob(EmptyC)
module P = NCicParamod(EmptyC)

type state = P.state
let empty_state = P.empty_state

exception NotEmbeddable 

let not_embeddable status subst context ty =
  let rec aux = function
    | NCic.Meta _
    | NCic.Const _
    | NCic.Rel _
    | NCic.Sort _ -> ()
    | NCic.Appl l -> List.iter aux l
    | t -> 
        (* cannot embed a blob term containing metas *)
        if (NCicUntrusted.metas_of_term status subst context t = [])
        then () 
        else raise NotEmbeddable
  in 
  try aux ty; noprint (lazy ("Embeddable")); false
  with NotEmbeddable -> debug (lazy ("Not embeddable")); true
;;

let tooflex (_,l,_,_) =
  match l with
    | Terms.Equation (l,r,_,o) ->
      (match l,r,o with
       | (Terms.Var _ | Terms.Node (Terms.Var _::_)), _, (Terms.Incomparable | Terms.Invertible) -> true
       | _, (Terms.Var _ | Terms.Node (Terms.Var _::_)),(Terms.Incomparable | Terms.Invertible) -> true
       | _ -> false)
    | _ -> false
;;  

let forward_infer_step0 status metasenv subst context s t ty =
  let bag = P.bag_of_state s in
  let not_embed =
    let sty,_,_ = 
      NCicMetaSubst.saturate status ~delta:0  metasenv subst context ty 0 in
      not_embeddable status subst context sty in
  if not_embed then (debug (lazy "theorem not embeddable"); s,None)
  else
  let bag,clause = P.mk_passive bag (t,ty) in
    if Terms.is_eq_clause clause then
      if tooflex clause then (debug (lazy "pruning tooflex"); s,None)
      else
       P.forward_infer_step (P.replace_bag s bag) clause 0, Some clause
    else (debug (lazy "not eq"); s,None)
;;

let forward_infer_step status metasenv subst context s t ty =
 fst (forward_infer_step0 status metasenv subst context s t ty)
;;

let index_obj status s uri =
  let obj = NCicEnvironment.get_checked_obj status uri in
  debug (lazy ("indexing : " ^ (NUri.string_of_uri uri)));
  debug (lazy ("no : " ^ (string_of_int (fst (Obj.magic uri)))));
  match obj with
    | (_,_,[],[],NCic.Constant(_,_,None,ty,_)) ->
        let nref = NReference.reference_of_spec uri NReference.Decl in
	forward_infer_step0 status [] [] [] s (NCic.Const nref) ty
    | (_,d,[],[],NCic.Constant(_,_,Some(_),ty,_)) ->
        let nref = NReference.reference_of_spec uri (NReference.Def d) in
	forward_infer_step0 status [] [] [] s (NCic.Const nref) ty
    | _ -> s,None
;;

let demod status metasenv subst context s goal =
  if not_embeddable status subst context (snd goal) then [] else
  (* let stamp = Unix.gettimeofday () in *)
  match P.demod s goal with
    | P.Error _ | P.GaveUp | P.Timeout _ -> []
    | P.Unsatisfiable solutions -> 
      (* print (lazy (Printf.sprintf "Got solutions in %fs"
		     (Unix.gettimeofday() -. stamp))); *)
      List.map (readback ~demod:true status metasenv subst context) solutions
;;

let paramod status metasenv subst context s goal =
  if not_embeddable status subst context (snd goal) then [] else
  (* let stamp = Unix.gettimeofday () in *)
  match P.nparamod ~useage:true ~max_steps:max_int 
    ~timeout:(Unix.gettimeofday () +. 300.0) s goal with
  | P.Error _ | P.GaveUp | P.Timeout _ -> []
  | P.Unsatisfiable solutions -> 
      (* print (lazy (Printf.sprintf "Got solutions in %fs"
		     (Unix.gettimeofday() -. stamp))); *)
      List.map (readback status metasenv subst context) solutions
;;

let fast_eq_check status metasenv subst context s goal =
  if not_embeddable status subst context (snd goal) then [] else
  (* let stamp = Unix.gettimeofday () in *)
  match P.fast_eq_check s goal with
  | P.Error _ | P.GaveUp | P.Timeout _ -> []
  | P.Unsatisfiable solutions -> 
      (* print (lazy (Printf.sprintf "Got solutions in %fs"
		     (Unix.gettimeofday() -. stamp))); *)
      List.map (readback status metasenv subst context) solutions
;;

let is_equation status metasenv subst context ty =
  let hty, _, _ = 
    NCicMetaSubst.saturate status ~delta:0 metasenv subst context
      ty 0 
  in match hty with
    | NCic.Appl (eq ::tl) when eq = CB.eqP -> true
    | _ -> false
;;

(*
let demodulate status metasenv subst context s goal =
  (* let stamp = Unix.gettimeofday () in *)
  match P.fast_eq_check s goal with
  | P.Error _ | P.GaveUp | P.Timeout _ -> []
  | P.Unsatisfiable solutions -> 
      (* print (lazy (Printf.sprintf "Got solutions in %fs"
		     (Unix.gettimeofday() -. stamp))); *)
      List.map (readback status metasenv subst context) solutions
;;
*)
