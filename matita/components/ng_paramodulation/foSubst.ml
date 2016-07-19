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

(* module Subst (B : Terms.Blob) = struct *)
  
  let id_subst = [];;
  
  let build_subst n t tail = (n,t) :: tail ;;
  
  let rec lookup var subst =
    match var with
      | Terms.Var i ->
          (try
            lookup (List.assoc i subst) subst
          with
              Not_found -> var)
      | _ -> var
  ;;
  let lookup i subst = lookup (Terms.Var i) subst;;
  
  let is_in_subst i subst = List.mem_assoc i subst;;
  
  (* filter out from metasenv the variables in substs *)
  let filter subst varlist =
    List.filter
      (fun m ->
         not (is_in_subst m subst))
      varlist
  ;;

  let rec reloc_subst subst = function
    | (Terms.Leaf _) as t -> t
    | Terms.Var i -> 
        (try
           List.assoc i subst
         with
             Not_found -> assert false)
    | (Terms.Node l) ->
	Terms.Node (List.map (fun t -> reloc_subst subst t) l)
;;

  let rec apply_subst subst = function
    | (Terms.Leaf _) as t -> t
    | Terms.Var i -> 
        (match lookup i subst with
        | Terms.Node _ as t -> apply_subst subst t
        | t -> t)
    | (Terms.Node l) ->
	Terms.Node (List.map (fun t -> apply_subst subst t) l)
;;

  let flat subst =
    List.map (fun (x,t) -> (x, apply_subst subst t)) subst
;;

  let concat x y = x @ y;;
  
(* end *)
