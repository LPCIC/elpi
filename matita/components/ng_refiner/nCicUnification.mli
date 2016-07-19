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

(* $Id: nCicUnification.mli 12479 2013-02-01 13:47:25Z fguidi $ *)

exception UnificationFailure of string Lazy.t;;
exception Uncertain of string Lazy.t;;
exception AssertFailure of string Lazy.t;;

val unify :
  #NCicCoercion.status ->
  ?test_eq_only:bool -> (* default: false *)
  ?swap:bool -> (* default: false *)
  NCic.metasenv -> NCic.substitution -> NCic.context -> 
  NCic.term -> NCic.term ->
   NCic.metasenv * NCic.substitution

(* this should be moved elsewhere *)
val fix_sorts: 
  #NCic.status -> NCic.metasenv -> NCic.substitution -> 
    NCic.term -> NCic.metasenv * NCic.term

(* this should be moved elsewhere *)
(* The term must be in whd *)
val could_reduce: #NCicCoercion.status -> subst:NCic.substitution -> NCic.context -> NCic.term -> bool

(* delift_type_wrt_terms st m s c t args
 *   lift t (length args) 
 *      [ rel 1 ... rel (len args) / lift (length args) (arg_1 .. arg_n) ]
 *)      
val delift_type_wrt_terms:
  #NCicCoercion.status -> 
  NCic.metasenv -> NCic.substitution -> NCic.context -> 
  NCic.term -> NCic.term list -> 
   NCic.metasenv * NCic.substitution * NCic.term

val sortfy :#
 NCic.status -> exn -> NCic.metasenv -> NCic.substitution -> NCic.context ->
  NCic.term -> NCic.metasenv * NCic.substitution * NCic.term

val indfy :#
 NCic.status -> exn -> NCic.metasenv -> NCic.substitution -> NCic.context ->
  NCic.term -> NCic.metasenv * NCic.substitution * NCic.term

val debug : bool ref
