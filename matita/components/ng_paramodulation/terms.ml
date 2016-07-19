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

(* $Id: terms.ml 10720 2010-02-08 07:24:34Z asperti $ *)

type 'a foterm = 
  | Leaf of 'a
  | Var of int
  | Node of ('a foterm) list

type 'a substitution = (int * 'a foterm) list

type comparison = Lt | Eq | Gt | Incomparable | Invertible

type rule = Superposition | Demodulation
type direction = Left2Right | Right2Left | Nodir
type position = int list

type 'a proof =
  | Exact of 'a foterm
  | Step of rule * int * int * direction * position * 'a substitution
         (* rule, eq1, eq2, direction of eq2, position, substitution *)

type 'a literal = 
 | Equation of    'a foterm  (* lhs *)
                * 'a foterm  (* rhs *)
                * 'a foterm  (* type *)
                * comparison (* orientation *)
 | Predicate of   'a foterm 

type varlist = int list

type 'a unit_clause =
   int        (* ID *)
 * 'a literal
 * varlist       (* variable list *)
 * 'a proof      (* proof *)

type 'a passive_clause = int * 'a unit_clause (* weight * equation *)

let is_eq_clause (_,l,_,_) =
  match l with
    | Equation _ -> true
    | Predicate _ -> false
;;

let vars_of_term t =
  let rec aux acc = function
    | Leaf _ -> acc
    | Var i -> if (List.mem i acc) then acc else i::acc
    | Node l -> List.fold_left aux acc l
  in aux [] t
;;

module OT =
 struct
   type t = int 
   let compare = Pervasives.compare
 end

module M : Map.S with type key = int 
  = Map.Make(OT) 

type 'a bag = int
              * (('a unit_clause * bool * int) M.t)

  let add_to_bag (_,lit,vl,proof) (id,bag) =
    let id = id+1 in
    let clause = (id, lit, vl, proof) in
    let bag = M.add id (clause,false,0) bag in
    (id,bag), clause 
   ;;

  let replace_in_bag ((id,_,_,_),_,_ as cl) (max_id,bag) =
    let bag = M.add id cl bag in
      (max_id,bag)
  ;;

  let get_from_bag id (_,bag) =
    M.find id bag
  ;;
    
  let empty_bag = (0,M.empty);;

module type Blob =
  sig
    type t
    val eq : t -> t -> bool
    val compare : t -> t -> int
    val eqP : t
    val is_eq: t foterm -> (t foterm* t foterm *t foterm) option 
    val pp : t -> string
    type input
    val embed : input -> t foterm
    val saturate : input -> input -> t foterm * t foterm
  end

