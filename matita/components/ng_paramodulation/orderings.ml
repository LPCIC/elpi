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

(* $Id: orderings.ml 12050 2012-05-17 11:26:24Z sacerdot $ *)

type aux_comparison = XEQ | XLE | XGE | XLT | XGT | XINCOMPARABLE | XINVERTIBLE

module type Blob =
  sig 
    include Terms.Blob 

    (* This order relation should be:
     * - stable for instantiation
     * - total on ground terms
     *
     *)
    val compare_terms : 
          t Terms.foterm -> t Terms.foterm -> Terms.comparison

    val compute_unit_clause_weight : 't Terms.unit_clause -> int

    val compute_goal_weight : 't Terms.unit_clause -> int

    val name : string

  end
  
type weight = int * (int * int) list;;
  
let rec eq_foterm f x y =
    x == y ||
    match x, y with
    | Terms.Leaf t1, Terms.Leaf t2 -> f t1 t2
    | Terms.Var i, Terms.Var j -> i = j
    | Terms.Node l1, Terms.Node l2 when List.length l1 = List.length l2 -> 
        List.for_all2 (eq_foterm f) l1 l2
    | _ -> false
;;
  
let string_of_weight (cw, mw) =
  let s =
    String.concat ", "
      (List.map (function (m, w) -> Printf.sprintf "(%d,%d)" m w) mw)
  in
  Printf.sprintf "[%d; %s]" cw s
;;
  
let weight_of_term term =
    let vars_dict = Hashtbl.create 5 in
    let rec aux = function
      | Terms.Var i -> 
          (try
             let oldw = Hashtbl.find vars_dict i in
             Hashtbl.replace vars_dict i (oldw+1)
           with Not_found ->
             Hashtbl.add vars_dict i 1);
          0
      | Terms.Leaf _ -> 1
      | Terms.Node l -> List.fold_left (+) 0 (List.map aux l)
    in
    let w = aux term in
    let l =
      Hashtbl.fold (fun meta metaw resw -> (meta, metaw)::resw) vars_dict [] 
    in
    let compare w1 w2 = 
      match w1, w2 with
      | (m1, _), (m2, _) -> m1 - m2
    in 
    (w, List.sort compare l) (* from the smallest meta to the bigest *)
;;
  
let compute_unit_clause_weight (_,l, _, _) = 
    let weight_of_polynomial w m =
      let factor = 2 in      
      w + factor * List.fold_left (fun acc (_,occ) -> acc+occ) 0 m
    in
    match l with
    | Terms.Predicate t -> 
        let w, m = weight_of_term t in 
        weight_of_polynomial w m
    | Terms.Equation (_,x,_,Terms.Lt) 
    | Terms.Equation (x,_,_,Terms.Gt) ->
        let w, m = weight_of_term x in 
        weight_of_polynomial w m
    | Terms.Equation (l,r,_,Terms.Eq) 
    | Terms.Equation (l,r,_,Terms.Incomparable) 
    | Terms.Equation (l,r,_,Terms.Invertible) ->
        let wl, ml = weight_of_term l in 
        let wr, mr = weight_of_term r in 
        weight_of_polynomial (wl+wr) (ml@mr)
;;

(* UNUSED for now *)
let compute_goal_weight (_,l, _, _) = 
    let weight_of_polynomial w m =
      let factor = 2 in      
      w + factor * List.fold_left (fun acc (_,occ) -> acc+occ) 0 m
    in
    match l with
    | Terms.Predicate t -> 
        let w, m = weight_of_term t in 
        weight_of_polynomial w m
    | Terms.Equation (l,r,_,_) ->
        let wl, ml = weight_of_term l in 
        let wr, mr = weight_of_term r in 
        let wl = weight_of_polynomial wl ml in
        let wr = weight_of_polynomial wr mr in
          - (abs (wl-wr))
  ;;

let compute_goal_weight = compute_unit_clause_weight;;
  
(* Riazanov: 3.1.5 pag 38 *)
(* Compare weights normalized in a new way :
 * Variables should be sorted from the lowest index to the highest
 * Variables which do not occur in the term should not be present
 * in the normalized polynomial
 *)
let compare_weights (h1, w1) (h2, w2) =
  let rec aux hdiff (lt, gt) diffs w1 w2 =
    match w1, w2 with
      | ((var1, w1)::tl1) as l1, (((var2, w2)::tl2) as l2) ->
          if var1 = var2 then
            let diffs = (w1 - w2) + diffs in
            let r = Pervasives.compare w1 w2 in
            let lt = lt or (r < 0) in
            let gt = gt or (r > 0) in
              if lt && gt then XINCOMPARABLE else
                aux hdiff (lt, gt) diffs tl1 tl2
          else if var1 < var2 then
            if lt then XINCOMPARABLE else
              aux hdiff (false,true) (diffs+w1) tl1 l2        
          else
            if gt then XINCOMPARABLE else
              aux hdiff (true,false) (diffs-w2) l1 tl2
      | [], (_,w2)::tl2 ->
          if gt then XINCOMPARABLE else
            aux hdiff (true,false) (diffs-w2) [] tl2
      | (_,w1)::tl1, [] ->
          if lt then XINCOMPARABLE else
            aux hdiff (false,true) (diffs+w1) tl1 []
      | [], [] ->
          if lt then
            if hdiff <= 0 then XLT
            else if (- diffs) >= hdiff then XLE else XINCOMPARABLE
          else if gt then
            if hdiff >= 0 then XGT
            else if diffs >= (- hdiff) then XGE else XINCOMPARABLE
          else
            if hdiff < 0 then XLT
            else if hdiff > 0 then XGT
            else XEQ
  in
    aux (h1-h2) (false,false) 0 w1 w2
;;

(* Riazanov: p. 40, relation >>> 
 * if head_only=true then it is not >>> but helps case 2 of 3.14 p 39 *)
let rec aux_ordering b_compare ?(head_only=false) t1 t2 =
  match t1, t2 with
  (* We want to discard any identity equality. *
   * If we give back XEQ, no inference rule    *
   * will be applied on this equality          *)
  | Terms.Var i, Terms.Var j when i = j ->
      XEQ
  (* 1. *)
  | Terms.Var _, _
  | _, Terms.Var _ -> XINCOMPARABLE
  (* 2.a *)
  | Terms.Leaf a1, Terms.Leaf a2 -> 
      let cmp = b_compare a1 a2 in
      if cmp = 0 then XEQ else if cmp < 0 then XLT else XGT
  | Terms.Leaf _, Terms.Node _ -> XLT
  | Terms.Node _, Terms.Leaf _ -> XGT
  (* 2.b *)
  | Terms.Node l1, Terms.Node l2 ->
      let rec cmp t1 t2 =
        match t1, t2 with
        | [], [] -> XEQ
        | _, [] -> (* XGT *) assert false (* hd symbols were eq *)
        | [], _ -> (* XLT *) assert false (* hd symbols were eq *)
        | hd1::tl1, hd2::tl2 ->
            let o = aux_ordering b_compare ~head_only hd1 hd2 in
            if o = XEQ && not head_only then cmp tl1 tl2 else o
      in
      cmp l1 l2
;;
  
let compare_terms o x y = 
    match o x y with
      | XINCOMPARABLE -> Terms.Incomparable
      | XGT -> Terms.Gt
      | XLT -> Terms.Lt
      | XEQ -> Terms.Eq
      | XINVERTIBLE -> Terms.Invertible
      | _ -> assert false
;;

module NRKBO (B : Terms.Blob) = struct
  let name = "nrkbo"
  include B 

  module Pp = Pp.Pp(B)

  let eq_foterm = eq_foterm B.eq;;

exception UnificationFailure of string Lazy.t;;


(* DUPLICATE CODE FOR TESTS (see FoUnif)  *)
  let alpha_eq s t =
    let rec equiv subst s t =
      let s = match s with Terms.Var i -> FoSubst.lookup i subst | _ -> s
      and t = match t with Terms.Var i -> FoSubst.lookup i subst | _ -> t
        
      in
      match s, t with
        | s, t when eq_foterm s t -> subst
        | Terms.Var i, Terms.Var j
            when (not (List.exists (fun (_,k) -> k=t) subst)) ->
            let subst = FoSubst.build_subst i t subst in
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
      equiv FoSubst.id_subst s t
;;

let relocate maxvar varlist subst =
    List.fold_right
      (fun i (maxvar, varlist, s) -> 
         maxvar+1, maxvar::varlist, FoSubst.build_subst i (Terms.Var maxvar) s)
      varlist (maxvar+1, [], subst)
  ;;

  let are_invertible l r =
    let varlist = (Terms.vars_of_term l)@(Terms.vars_of_term r) in
    let maxvar = List.fold_left max 0 varlist in
    let _,_,subst = relocate maxvar varlist FoSubst.id_subst in
    let newl = FoSubst.apply_subst subst l in
    let newr = FoSubst.apply_subst subst r in
      try (let subst = alpha_eq l newr in eq_foterm newl (FoSubst.apply_subst subst r)) with
	  UnificationFailure _ -> false
;;

  let compute_unit_clause_weight = compute_unit_clause_weight;;
  let compute_goal_weight = compute_goal_weight;;
  
  (* Riazanov: p. 40, relation >_n *)
  let nonrec_kbo t1 t2 =
    let w1 = weight_of_term t1 in
    let w2 = weight_of_term t2 in
    match compare_weights w1 w2 with
    | XLE ->  (* this is .> *)
        if aux_ordering B.compare t1 t2 = XLT then XLT else XINCOMPARABLE
    | XGE -> 
        if aux_ordering B.compare t1 t2 = XGT then XGT else XINCOMPARABLE
    | XEQ -> let res = aux_ordering B.compare t1 t2 in
	if res = XINCOMPARABLE && are_invertible t1 t2 then XINVERTIBLE
	else res
    | res -> res
  ;;

  let compare_terms = compare_terms nonrec_kbo;;

  let profiler = HExtlib.profile ~enable:true "compare_terms(nrkbo)";;
  let compare_terms x y =
    profiler.HExtlib.profile (compare_terms x) y
  ;;

end
  
module KBO (B : Terms.Blob) = struct
  let name = "kbo"
  include B 

  module Pp = Pp.Pp(B)

  let eq_foterm = eq_foterm B.eq;;

  let compute_unit_clause_weight = compute_unit_clause_weight;;
  let compute_goal_weight = compute_goal_weight;;

  (* Riazanov: p. 38, relation > *)
  let rec kbo t1 t2 =
    let aux = aux_ordering B.compare ~head_only:true in
    let rec cmp t1 t2 =
      match t1, t2 with
      | [], [] -> XEQ
      | _, [] -> XGT
      | [], _ -> XLT
      | hd1::tl1, hd2::tl2 ->
          let o = kbo hd1 hd2 in
          if o = XEQ then cmp tl1 tl2
          else o
    in
    let w1 = weight_of_term t1 in
    let w2 = weight_of_term t2 in
    let comparison = compare_weights w1 w2 in
    match comparison with
    | XLE ->
        let r = aux t1 t2 in
        if r = XLT then XLT
        else if r = XEQ then (
          match t1, t2 with
          | Terms.Node (_::tl1), Terms.Node (_::tl2) ->
              if cmp tl1 tl2 = XLT then XLT else XINCOMPARABLE
          | _, _ -> assert false
        ) else XINCOMPARABLE
    | XGE ->
        let r = aux t1 t2 in
        if r = XGT then XGT
        else if r = XEQ then (
          match t1, t2 with
          | Terms.Node (_::tl1), Terms.Node (_::tl2) ->
              if cmp tl1 tl2 = XGT then XGT else XINCOMPARABLE
          | _, _ ->  assert false
        ) else XINCOMPARABLE
    | XEQ ->
        let r = aux t1 t2 in
        if r = XEQ then (
          match t1, t2 with
	  | Terms.Var i, Terms.Var j when i=j -> XEQ
          | Terms.Node (_::tl1), Terms.Node (_::tl2) -> cmp tl1 tl2
          | _, _ ->  XINCOMPARABLE
        ) else r 
    | res -> res
  ;;

  let compare_terms = compare_terms kbo;;

  let profiler = HExtlib.profile ~enable:true "compare_terms(kbo)";;
  let compare_terms x y =
    profiler.HExtlib.profile (compare_terms x) y
  ;;

end

module LPO (B : Terms.Blob) = struct
  let name = "lpo"
  include B 

  module Pp = Pp.Pp(B)

  let eq_foterm = eq_foterm B.eq;;

  let compute_unit_clause_weight = compute_unit_clause_weight;;
  let compute_goal_weight = compute_goal_weight;;

  (*CSC: beware! Imperative cache! *)
  let cache = Hashtbl.create 101

  let rec lpo_le s t = 
    eq_foterm s t || lpo_lt s t 
  
  and lpo_lt s t =
    try Hashtbl.find cache (s,t)
    with
    Not_found -> let res =
    match s,t with
      | _, Terms.Var _ -> false
      | Terms.Var i,_ ->
          if (List.mem i (Terms.vars_of_term t)) then true
          else false
      | Terms.Leaf a, Terms.Leaf b -> B.compare a b < 0
      | Terms.Leaf _, Terms.Node _  -> true (* we assume unary constants 
                            are smaller than constants with higher arity *)
      | Terms.Node _, Terms.Leaf _ -> false
      | Terms.Node [],_
      | _,Terms.Node [] -> assert false
      | Terms.Node (hd1::tl1), Terms.Node (hd2::tl2) ->
          if List.exists (lpo_le s) tl2 then true
          else
          begin 
            match aux_ordering B.compare hd1 hd2 with
            | XINCOMPARABLE 
            | XGT -> false
            | XLT -> List.for_all (fun x -> lpo_lt x t) tl1
            | XEQ -> 
                let rec compare_args l1 l2 =
                match l1,l2 with
                | [],_ 
                | _,[] -> false
                | a1::tl1,a2::tl2 -> 
                    if eq_foterm a1 a2 then compare_args tl1 tl2
                    else if lpo_lt a1 a2 then List.for_all (fun x -> lpo_lt x t) tl1
                    else false
                in 
                compare_args tl1 tl2
            | _ -> assert false
           end
   in
    Hashtbl.add cache (s,t) res; res
  ;;

  let lpo s t =
    let res =
    if eq_foterm s t then XEQ
    else if lpo_lt s t then XLT
    else if lpo_lt t s then XGT
    else XINCOMPARABLE
    in
     Hashtbl.clear cache; res
  ;;
    

  let compare_terms = compare_terms lpo;;

  let profiler = HExtlib.profile ~enable:true "compare_terms(lpo)";;
  let compare_terms x y =
    profiler.HExtlib.profile (compare_terms x) y
  ;;

end

