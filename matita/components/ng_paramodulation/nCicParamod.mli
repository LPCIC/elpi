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

val nparamod :
  #NCicCoercion.status ->
  NCic.metasenv -> NCic.substitution -> NCic.context -> 
    (NCic.term * NCic.term) -> (NCic.term * NCic.term) list ->
     (NCic.term * NCic.term * NCic.metasenv * NCic.substitution) list

type state 
val empty_state: state
val forward_infer_step: 
  #NCic.status -> NCic.metasenv -> NCic.substitution -> NCic.context ->
  state -> NCic.term -> NCic.term -> state
val index_obj:
 #NCic.status -> state -> NUri.uri -> state * NCic.term Terms.unit_clause option
val is_equation:
 #NCic.status -> NCic.metasenv -> NCic.substitution -> NCic.context ->
  NCic.term -> bool
val paramod : 
  #NCicCoercion.status ->
  NCic.metasenv -> NCic.substitution -> NCic.context ->
  state -> 
  (NCic.term * NCic.term) -> 
  (NCic.term * NCic.term * NCic.metasenv * NCic.substitution) list
val fast_eq_check : 
  #NCicCoercion.status ->
  NCic.metasenv -> NCic.substitution -> NCic.context ->
  state -> 
  (NCic.term * NCic.term) -> 
  (NCic.term * NCic.term * NCic.metasenv * NCic.substitution) list
val demod : 
  #NCicCoercion.status ->
  NCic.metasenv -> NCic.substitution -> NCic.context ->
  state -> 
  (NCic.term * NCic.term) -> 
  (NCic.term * NCic.term * NCic.metasenv * NCic.substitution) list
