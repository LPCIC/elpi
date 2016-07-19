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

(* $Id: terms.mli 9822 2009-06-03 15:37:06Z tassi $ *)

let eqPref = ref (fun _ -> assert false);;
let set_eqP t = eqPref := fun _ -> t;;

let default_eqP() =
  let uri = NUri.uri_of_string "cic:/matita/basics/logic/eq.ind" in
  let ref = NReference.reference_of_spec uri (NReference.Ind(true,0,2)) in
    NCic.Const ref
;;

let equivalence_relation =
  let uri = NUri.uri_of_string "cic:/matita/ng/properties/relations/eq_rel.con"
  in
  let ref = NReference.reference_of_spec uri (NReference.Fix(0,1,2)) 
  in NCic.Const ref

let setoid_eq =
  let uri = NUri.uri_of_string "cic:/matita/ng/sets/setoids/eq.con" in
  let ref = NReference.reference_of_spec uri (NReference.Fix(0,0,2)) 
  in NCic.Const ref

let set_default_eqP() = eqPref := default_eqP

module type NCicContext =
  sig
    val metasenv : NCic.metasenv
    val subst : NCic.substitution
    val context : NCic.context
  end

module NCicBlob(C : NCicContext) : Terms.Blob 
with type t = NCic.term and type input = NCic.term = struct

  type t = NCic.term

  let eq x y =
   (* CSC: NCicPp.status is the best I can put here *)
   x = y ||
   NCicReduction.alpha_eq (new NCicPp.status) C.metasenv C.subst C.context x y;;

  let height_of_ref = function
    | NReference.Def h -> h
    | NReference.Fix(_,_,h) -> h
    | _ -> 0

external old_hash_param :
  int -> int -> 'a -> int = "caml_hash_univ_param" "noalloc";;

let old_hash = old_hash_param 10 100;;

  let compare_refs (NReference.Ref (u1,r1)) (NReference.Ref (u2,r2)) =
    let x = height_of_ref r2 - height_of_ref r1 in
      if x = 0 then 
	old_hash (NUri.string_of_uri u1,r1) - 
	  old_hash (NUri.string_of_uri u2,r2)
      else x 

  let rec compare x y = 
    match x,y with
    | NCic.Rel i, NCic.Rel j -> j-i
    | NCic.Meta (i,_), NCic.Meta (j,_) -> i-j
    | NCic.Const r1, NCic.Const r2 -> compare_refs r1 r2
    (*NReference.compare r1 r2*)
    | NCic.Appl l1, NCic.Appl l2 -> FoUtils.lexicograph compare l1 l2
    | NCic.Rel _, ( NCic.Meta _ | NCic.Const _ | NCic.Appl _ ) -> ~-1
    | ( NCic.Meta _ | NCic.Const _ | NCic.Appl _ ), NCic.Rel _ -> 1
    | NCic.Const _, ( NCic.Meta _ | NCic.Appl _ ) -> ~-1
    | ( NCic.Meta _ | NCic.Appl _ ), NCic.Const _ -> 1
    | NCic.Appl _, NCic.Meta _ -> ~-1
    | NCic.Meta _, NCic.Appl _ -> 1
    | _ -> Pervasives.compare x y
	(* was assert false, but why? *)
	
  ;;
  
  let compare x y = 
    if eq x y then 0
    else compare x y
  ;;

  let eqP = (!eqPref)()
  ;;

  let is_eq = function
    | Terms.Node [ Terms.Leaf eqt ; ty; l; r ] when eq eqP eqt ->
        Some (ty,l,r) 
(*
    | Terms.Node [ Terms.Leaf eqt ; _; Terms.Node [Terms.Leaf eqt2 ; ty]; l; r]
	when eq equivalence_relation eqt && eq setoid_eq eqt2 ->
        Some (ty,l,r) *)
    | _ -> None

  let pp t = 
    (* CSC: NCicPp.status is the best I can put here *)
    (new NCicPp.status)#ppterm ~context:C.context
      ~metasenv:C.metasenv ~subst:C.subst t;;

  type input = NCic.term

  let rec embed = function
    | NCic.Meta (i,_) -> Terms.Var i, [i]
    | NCic.Appl l ->
	let rec aux acc l = function
	  |[] -> acc@l
	  |hd::tl -> if List.mem hd l then aux acc l tl else aux (hd::acc) l tl
	in
	let res,vars = List.fold_left
	  (fun (r,v) t -> let r1,v1 = embed t in (r1::r),aux [] v v1) ([],[]) l
	in (Terms.Node (List.rev res)), vars
    | t -> Terms.Leaf t, []
  ;;

  let embed t = fst (embed t) ;;

  let saturate t ty = 
    let sty, _, args = 
      (* CSC: NCicPp.status is the best I can put here *)
      NCicMetaSubst.saturate (new NCicPp.status) ~delta:0 C.metasenv C.subst
       C.context ty 0
    in
    let proof = 
      if args = [] then Terms.Leaf t 
      else Terms.Node (Terms.Leaf t :: List.map embed args)
    in
    let sty = embed sty in
    proof, sty
  ;;
  
 end
