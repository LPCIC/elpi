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

(* $Id: nCicUntrusted.mli 11172 2011-01-11 21:06:37Z sacerdot $ *)

val map_term_fold_a:
 #NCic.status ->
 (NCic.hypothesis -> 'k -> 'k) -> 'k ->
 ('k -> 'a -> NCic.term -> 'a * NCic.term) -> 'a -> NCic.term -> 'a * NCic.term

val map_obj_kind: 
  ?skip_body:bool -> (NCic.term -> NCic.term) -> NCic.obj_kind -> NCic.obj_kind

val metas_of_term :
 #NCic.status -> NCic.substitution -> NCic.context -> NCic.term -> int list
val sort_metasenv:
 #NCic.status -> NCic.substitution -> NCic.metasenv -> NCic.metasenv

type meta_kind = [ `IsSort | `IsType | `IsTerm ]
val kind_of_meta: NCic.meta_attrs -> meta_kind
val set_kind: meta_kind -> NCic.meta_attrs -> NCic.meta_attrs 
val replace_in_metasenv: 
  int -> (NCic.conjecture -> NCic.conjecture) -> NCic.metasenv -> NCic.metasenv
val replace_in_subst: 
  int -> (NCic.subst_entry -> NCic.subst_entry) -> NCic.substitution ->
   NCic.substitution
val max_kind: meta_kind -> meta_kind -> meta_kind

module NCicHash : Hashtbl.S with type key = NCic.term

val mk_appl : NCic.term -> NCic.term list -> NCic.term 

(* the context is needed only to honour Barendregt's naming convention *)
val apply_subst :
 #NCic.status -> NCic.substitution -> NCic.context -> NCic.term -> NCic.term
val apply_subst_context :
 #NCic.status -> fix_projections:bool -> 
  NCic.substitution -> NCic.context -> NCic.context
val apply_subst_metasenv :
 #NCic.status -> NCic.substitution -> NCic.metasenv -> NCic.metasenv

val count_occurrences :
 #NCic.status -> subst:NCic.substitution -> int -> NCic.term -> int
(* quick, but with false negatives (since no ~subst), check for closed terms *)
val looks_closed : NCic.term -> bool
