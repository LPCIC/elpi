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

(* $Id: nCicReduction.mli 11172 2011-01-11 21:06:37Z sacerdot $ *)

exception AssertFailure of string Lazy.t;;

val debug: bool ref

val whd : 
  #NCic.status -> ?delta:int -> subst:NCic.substitution -> 
  NCic.context -> NCic.term -> NCic.term

val set_get_relevance : 
  (NCic.status -> metasenv:NCic.metasenv -> subst:NCic.substitution ->
   NCic.context -> NCic.term -> NCic.term list -> bool list) -> unit

val are_convertible :
  #NCic.status -> metasenv:NCic.metasenv -> subst:NCic.substitution ->
  NCic.context -> NCic.term -> NCic.term -> bool


(* performs head beta/(delta)/cast reduction; the default is to not perform
   delta reduction; if provided, ~upto is the maximum number of beta redexes
   reduced *)
val head_beta_reduce: 
 #NCic.status -> ?delta:int -> ?upto:int -> ?subst:NCic.substitution ->
  NCic.term -> NCic.term

type stack_item
type environment_item

type machine = int * environment_item list * NCic.term * stack_item list

val reduce_machine : 
 #NCic.status -> delta:int -> ?subst:NCic.substitution -> NCic.context ->
  machine -> machine * bool
val from_stack : delta:int -> stack_item -> machine
val from_env : delta:int -> environment_item -> machine
val unwind : #NCic.status -> machine -> NCic.term

val split_prods:
 #NCic.status -> subst:NCic.substitution -> NCic.context -> int -> NCic.term ->
  NCic.context * NCic.term

(* to be used outside the kernel *)
val alpha_eq:
 #NCic.status -> NCic.metasenv -> NCic.substitution -> NCic.context ->
  NCic.term -> NCic.term -> bool
