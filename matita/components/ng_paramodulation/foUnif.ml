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

(* $Id: nCic.ml 9058 2008-10-13 17:42:30Z tassi $ *)

exception UnificationFailure of string Lazy.t;;

let mem2 a b l =
  let rec aux found_a found_b = function
    | x :: tl ->
       let found_a = found_a || x = a in
       let found_b = found_b || x = b in
       if found_a && found_b then true, true
       else aux found_a found_b tl
    | [] -> found_a, found_b
  in
   aux false false l
;;

module Founif (B : Orderings.Blob) = struct
  module Subst = FoSubst 
  module U = FoUtils.Utils(B)

  let unification (* vars *) locked_vars t1 t2 =
    let rec occurs_check subst what where =
      match where with
      | Terms.Var i when i = what -> true
      | Terms.Var i ->
          let t = Subst.lookup i subst in
          if not (U.eq_foterm t where) then occurs_check subst what t else false
      | Terms.Node l -> List.exists (occurs_check subst what) l
      | _ -> false
    in
    let rec unif subst s t =
      let s = match s with Terms.Var i -> Subst.lookup i subst | _ -> s
      and t = match t with Terms.Var i -> Subst.lookup i subst | _ -> t
      
      in
      match s, t with
      | s, t when U.eq_foterm s t -> subst
      | Terms.Var i, Terms.Var j ->
          (* TODO: look in locked vars for both i and j at once *)
          let i_locked, j_locked = mem2 i j locked_vars in
          if i_locked then
            if j_locked then
              raise (UnificationFailure (lazy "Inference.unification.unif"))
            else
              Subst.build_subst j s subst
          else
            Subst.build_subst i t subst
      | Terms.Var i, t when occurs_check subst i t ->
          raise (UnificationFailure (lazy "Inference.unification.unif"))
      | Terms.Var i, t when (List.mem i locked_vars) -> 
          raise (UnificationFailure (lazy "Inference.unification.unif"))
      | Terms.Var i, t -> Subst.build_subst i t subst
      | t, Terms.Var i when occurs_check subst i t ->
          raise (UnificationFailure (lazy "Inference.unification.unif"))
      | t, Terms.Var i when (List.mem i locked_vars) -> 
          raise (UnificationFailure (lazy "Inference.unification.unif"))
      | t, Terms.Var i -> Subst.build_subst i t subst
      | Terms.Node l1, Terms.Node l2 -> (
          try
            List.fold_left2
              (fun subst' s t -> unif subst' s t)
              subst l1 l2
          with Invalid_argument _ ->
            raise (UnificationFailure (lazy "Inference.unification.unif"))
        )
      | _, _ ->
          raise (UnificationFailure (lazy "Inference.unification.unif"))
    in
    let subst = unif Subst.id_subst t1 t2 in
    subst
;;

(* Sets of variables in s and t are assumed to be disjoint  *)
  let alpha_eq s t =
    let rec equiv subst s t =
      let s = match s with Terms.Var i -> Subst.lookup i subst | _ -> s
      and t = match t with Terms.Var i -> Subst.lookup i subst | _ -> t
        
      in
      match s, t with
        | s, t when U.eq_foterm s t -> subst
        | Terms.Var i, Terms.Var j
            when (not (List.exists (fun (_,k) -> k=t) subst)) ->
            let subst = Subst.build_subst i t subst in
              subst
        | Terms.Node l1, Terms.Node l2 -> (
            try
              List.fold_left2
                (fun subst' s t -> equiv subst' s t)
                subst l1 l2
            with Invalid_argument _ ->
              raise (UnificationFailure (lazy "Inference.unification.unif"))
          )
        | _, _ ->
            raise (UnificationFailure (lazy "Inference.unification.unif"))
    in
      equiv Subst.id_subst s t
;;
	

end
