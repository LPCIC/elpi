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

module type Paramod =
  sig
    type t
    type input
    type state
    type szsontology = 
      | Unsatisfiable of 
	  (t Terms.bag * int * t Terms.substitution * int list) list
      | GaveUp 
      | Error of string 
      | Timeout of int * t Terms.bag
    type bag = t Terms.bag * int
    val empty_state : state
    val bag_of_state :state -> bag
    val replace_bag : state -> bag -> state
    val mk_passive : bag -> input * input -> bag * t Terms.unit_clause
    val mk_goal : bag -> input * input -> bag * t Terms.unit_clause
    val forward_infer_step :       
      state ->
      t Terms.unit_clause ->
      int ->
      state 
    val goal_narrowing :
      int 
      -> int
      -> float option
      -> state
      -> state       
    val paramod : 
      useage:bool ->
      max_steps:int ->
      ?timeout:float ->
      bag -> 
      g_passives:t Terms.unit_clause list -> 
      passives:t Terms.unit_clause list -> szsontology
    val demod :
      state -> input* input -> szsontology
    val fast_eq_check :
      state -> input* input -> szsontology
    val nparamod :
      useage:bool ->
      max_steps:int ->
      ?timeout:float ->
      state -> 
      input* input -> 
      szsontology
  end

module Paramod ( B : Orderings.Blob ) : Paramod
with type t = B.t and type input = B.input
