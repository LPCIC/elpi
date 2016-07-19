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

(* $Id: nCicTypeChecker.mli 13212 2016-06-13 16:27:50Z fguidi $ *)

(* These are the only exceptions that will be raised *)
exception TypeCheckerFailure of string Lazy.t
exception AssertFailure of string Lazy.t

val set_logger: 
  ([ `Start_type_checking of NUri.uri 
   | `Type_checking_completed of NUri.uri
   | `Type_checking_interrupted of NUri.uri
   | `Type_checking_failed of NUri.uri
   | `Trust_obj of NUri.uri
   ] -> unit) -> unit

val set_trust : (NCic.obj -> bool) -> unit

val typeof: 
 #NCic.status -> subst:NCic.substitution -> metasenv:NCic.metasenv -> 
  NCic.context -> NCic.term -> NCic.term

val height_of_obj_kind:
 #NCic.status -> NUri.uri -> subst:NCic.substitution -> NCic.obj_kind -> int

val get_relevance : 
 #NCic.status ->
  metasenv:NCic.metasenv -> subst:NCic.substitution ->
  NCic.context -> NCic.term -> NCic.term list -> bool list

(* type_of_branch subst context leftno outtype 
 *   (constr @ lefts) (ty_constr @ lefts)  *)
val type_of_branch : 
 #NCic.status ->
  subst:NCic.substitution ->
    NCic.context -> int -> NCic.term -> NCic.term -> NCic.term -> 
     NCic.term

(* ind = indtype @ lefts
 * arity1 = constructor type @ lefts
 * arity2 = outtype *)
val check_allowed_sort_elimination : 
 #NCic.status ->
  subst:NCic.substitution ->
  metasenv:NCic.metasenv ->
  NReference.reference -> NCic.context -> 
    NCic.term -> NCic.term -> NCic.term -> unit

(* Functions to be used by the refiner *)
val debruijn:
 #NCic.status -> NUri.uri -> int -> subst:NCic.substitution -> NCic.context ->
  NCic.term -> NCic.term

val are_all_occurrences_positive: 
 #NCic.status -> subst:NCic.substitution -> NCic.context -> NUri.uri -> int ->
  int -> int -> int -> NCic.term -> bool

(* does_not_occur ... n nn t
 * detects the Rels m of t in the range n < m <= nn
 * recursively delta-expanding the Rels m of t in the range 0 < m <= n
 *)
val does_not_occur :
 #NCic.status -> subst:NCic.substitution -> NCic.context -> int -> int ->
  NCic.term -> bool
