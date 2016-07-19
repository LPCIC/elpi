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

(* $Id: terms.ml 9836 2009-06-05 15:33:35Z denes $ *)

let rec lexicograph f l1 l2 =
  match l1, l2 with
  | [], [] -> 0
  | x::xs, y::ys ->
     let c = f x y in
     if c <> 0 then c else lexicograph f xs ys
  | [],_ -> ~-1
  | _,[] -> 1
;;
  
module Utils (B : Orderings.Blob) = struct
  module Subst = FoSubst;; 
  module Order = B;;

  let rec eq_foterm x y =
    x == y ||
    match x, y with
    | Terms.Leaf t1, Terms.Leaf t2 -> B.eq t1 t2 
    | Terms.Var i, Terms.Var j -> i = j
    | Terms.Node l1, Terms.Node l2 -> List.for_all2 eq_foterm l1 l2
    | _ -> false
  ;;


  let rec compare_foterm x y =
    match x, y with
    | Terms.Leaf t1, Terms.Leaf t2 -> B.compare t1 t2
    | Terms.Var i, Terms.Var j -> i - j
    | Terms.Node l1, Terms.Node l2 -> lexicograph compare_foterm l1 l2
    | Terms.Leaf _, ( Terms.Node _ | Terms.Var _ ) -> ~-1
    | Terms.Node _, Terms.Leaf _ -> 1
    | Terms.Node _, Terms.Var _ -> ~-1
    | Terms.Var _, _ ->  1
  ;;

  let eq_literal l1 l2 =
    match l1, l2 with
    | Terms.Predicate p1, Terms.Predicate p2 -> eq_foterm p1 p2
    | Terms.Equation (l1,r1,ty1,o1), Terms.Equation (l2,r2,ty2,o2) ->
        o1 = o2 && eq_foterm l1 l2 && eq_foterm r1 r2 && eq_foterm ty1 ty2
    | _ -> false
  ;;

  let compare_literal l1 l2 =
    match l1, l2 with
    | Terms.Predicate p1, Terms.Predicate p2 -> compare_foterm p1 p2
    | Terms.Equation (l1,r1,ty1,o1), Terms.Equation (l2,r2,ty2,o2) ->
        let c = Pervasives.compare o1 o2 in
        if c <> 0 then c else
          let c = compare_foterm l1 l2 in
          if c <> 0 then c else
            let c = compare_foterm r1 r2 in
            if c <> 0 then c else
              compare_foterm ty1 ty2
    | Terms.Predicate _, Terms.Equation _ -> ~-1
    | Terms.Equation _, Terms.Predicate _ -> 1
  ;;

  let eq_unit_clause (id1,_,_,_) (id2,_,_,_) = id1 = id2
  let compare_unit_clause (id1,_,_,_) (id2,_,_,_) = Pervasives.compare id1 id2
    
  let relocate maxvar varlist subst =
    List.fold_right
      (fun i (maxvar, varlist, s) -> 
         maxvar+1, maxvar::varlist, Subst.build_subst i (Terms.Var maxvar) s)
      varlist (maxvar+1, [], subst)
  ;;

  let fresh_unit_clause maxvar (id, lit, varlist, proof) =
    (* prerr_endline 
      ("varlist = " ^ (String.concat "," (List.map string_of_int varlist)));*)
    let maxvar, varlist, subst = relocate maxvar varlist Subst.id_subst in
    let lit = 
      match lit with
      | Terms.Equation (l,r,ty,o) ->
          let l = Subst.reloc_subst subst l in
          let r = Subst.reloc_subst subst r in
          let ty = Subst.reloc_subst subst ty in
          Terms.Equation (l,r,ty,o)
      | Terms.Predicate p ->
          let p = Subst.reloc_subst subst p in
          Terms.Predicate p
    in
    let proof =
      match proof with
      | Terms.Exact t -> Terms.Exact (Subst.reloc_subst subst t)
      | Terms.Step (rule,c1,c2,dir,pos,s) ->
          Terms.Step(rule,c1,c2,dir,pos,Subst.concat subst s)
    in
     (id, lit, varlist, proof), maxvar
  ;;

  (* may be moved inside the bag *)
  let mk_unit_clause maxvar ty proofterm =
    let varlist =
      let rec aux acc = function
        | Terms.Leaf _ -> acc
        | Terms.Var i -> if List.mem i acc then acc else i::acc
        | Terms.Node l -> List.fold_left aux acc l 
      in
       aux (aux [] ty) proofterm
    in
    let lit = 
      match B.is_eq ty with
      | Some(ty,l,r) ->
           let o = Order.compare_terms l r in
           Terms.Equation (l, r, ty, o)
      | None -> Terms.Predicate ty
    in
    let proof = Terms.Exact proofterm in
    fresh_unit_clause maxvar (0, lit, varlist, proof)
  ;;

  let mk_passive_clause cl =
    (Order.compute_unit_clause_weight cl, cl)
  ;;

  let mk_passive_goal g =
    (Order.compute_unit_clause_weight g, g)
  ;;

  let compare_passive_clauses_weight (w1,(id1,_,_,_)) (w2,(id2,_,_,_)) =
    if w1 = w2 then id1 - id2
    else w1 - w2
  ;;

  let compare_passive_clauses_age (_,(id1,_,_,_)) (_,(id2,_,_,_)) =
    id1 - id2
  ;;

end
