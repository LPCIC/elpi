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

(* $Id: nCicUtils.mli 11172 2011-01-11 21:06:37Z sacerdot $ *)

exception Subst_not_found of int
exception Meta_not_found of int

val expand_local_context : NCic.lc_kind -> NCic.term list

val lookup_subst: int ->  NCic.substitution -> NCic.subst_entry
val lookup_meta: int ->  NCic.metasenv -> NCic.conjecture

(* both functions raise "assert false" when a Meta is found
 * call the 'a->'a function when a binder is crossed *)
val fold:
  (NCic.hypothesis -> 'k -> 'k) -> 'k ->
  ('k -> 'a -> NCic.term -> 'a) -> 'a -> NCic.term -> 'a
val map:
 #NCic.status ->
 (NCic.hypothesis -> 'k -> 'k) -> 'k ->
 ('k -> NCic.term -> NCic.term) -> NCic.term -> NCic.term

val set_head_beta_reduce: (NCic.status -> upto:int -> NCic.term -> NCic.term) -> unit

