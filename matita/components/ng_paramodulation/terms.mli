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

(* $Id: terms.mli 10720 2010-02-08 07:24:34Z asperti $ *)

type 'a foterm = 
  | Leaf of 'a
  | Var of int
  | Node of ('a foterm) list

type 'a substitution = (int * 'a foterm) list

type comparison = Lt | Eq | Gt | Incomparable | Invertible

type rule = Superposition | Demodulation

(* A Discrimination tree is a map: foterm |-> (dir, clause) *)
type direction = Left2Right | Right2Left | Nodir

type position = int list

type 'a proof =
  | Exact of 'a foterm
         (* for theorems like T : \forall x. C[x] = D[x] the proof is 
          * a foterm like (Node [ Leaf T ; Var i ]), while for the Goal
          * it is just (Var g), i.e. the identity proof *)
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
 * varlist
 * 'a proof      (* proof *)

type 'a passive_clause = int * 'a unit_clause (* weight * equation *)

val is_eq_clause : 'a unit_clause -> bool
val vars_of_term : 'a foterm -> int list

module M : Map.S with type key = int 

type 'a bag = int (* max ID  *)
              * (('a unit_clause * bool * int) M.t)

(* also gives a fresh ID to the clause *)
    val add_to_bag : 
          'a unit_clause -> 'a bag ->
            'a bag * 'a unit_clause

    val replace_in_bag : 
          'a unit_clause * bool * int -> 'a bag ->
            'a bag

    val get_from_bag : 
          int -> 'a bag -> 'a unit_clause * bool * int

    val empty_bag : 'a bag

module type Blob =
  sig
    (* Blob is the type for opaque leaves: 
     * - checking equlity should be efficient
     * - atoms have to be equipped with a total order relation
     *)
    type t
    val eq : t -> t -> bool
    val compare : t -> t -> int
    val eqP : t
    (* TODO: consider taking in input an imperative buffer for Format 
     *  val pp : Format.formatter -> t -> unit
     * *)
    val is_eq : t foterm -> (t foterm * t foterm * t foterm) option
    val pp : t -> string

    type input
    val embed : input -> t foterm
    (* saturate [proof] [type] -> [proof] * [type] *)
    val saturate : input -> input -> t foterm * t foterm

  end

