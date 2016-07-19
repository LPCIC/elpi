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

(* $Id: nCicMetaSubst.mli 12531 2013-02-27 20:19:04Z sacerdot $ *)

exception MetaSubstFailure of string Lazy.t
exception Uncertain of string Lazy.t

val debug: bool ref

(* the index of the last created meta *)
val maxmeta: unit -> int

(* Bad, this should be made functional and put in the status! *)
val pushmaxmeta: unit -> unit
val popmaxmeta: unit -> unit

(* the delift function takes in input a metavariable index, a local_context
 * and a term t, and substitutes every subterm t' of t with its position 
 * (searched up-to unification) in
 * the local_context (which is the Rel moved to the canonical context).
 * Typically, the list of optional terms is the explicit
 * substitution that is applied to a metavariable occurrence and the result of
 * the delift function is a term the implicit variable can be substituted with
 * to make the term [t] unifiable with the metavariable occurrence.  In general,
 * the problem is undecidable if we consider equivalence in place of alpha
 * convertibility.
 * The old implementation, though, is even weaker than alpha
 * convertibility, since it replace the term [tk] if and only if [tk] is a Rel
 * (missing all the other cases). Does this matter in practice?
 * The new experimental implementation, instead, works up to unification.
 * The metavariable index is the index of the metavariable that must not occur
 * in the term (for occur check).
 *)
val delift : 
  #NCic.status ->
  unify:(NCic.metasenv -> NCic.substitution -> NCic.context ->
    NCic.term -> NCic.term -> (NCic.metasenv * NCic.substitution) option) -> 
  NCic.metasenv -> NCic.substitution -> NCic.context -> 
  int -> NCic.local_context -> NCic.term ->
    (NCic.metasenv * NCic.substitution) * NCic.term

(* restrict metasenv subst n l
   returns metasenv, subst, created meta and l' where l' is the list of
   additional (i.e. l' does not intersects l) positions whose restriction was
   forced because of type dependencies *)
val restrict: 
   #NCic.status ->
    NCic.metasenv ->
    NCic.substitution ->
    int -> int list ->
     NCic.metasenv * NCic.substitution * int * int list

(* bool = true if the type of the new meta is closed *)
val mk_meta: 
   ?attrs:NCic.meta_attrs -> 
   NCic.metasenv -> NCic.context -> 
    ?with_type:NCic.term -> NCicUntrusted.meta_kind ->
    NCic.metasenv * int * NCic.term * NCic.term (* menv,metano,instance,type *)

(* extend_meta m n: n must be in m *)
val extend_meta: NCic.metasenv -> int -> NCic.metasenv * NCic.term

(* returns the resulting type, the metasenv and the arguments *)
val saturate:
   #NCic.status ->
    ?delta:int -> NCic.metasenv -> NCic.substitution -> 
    NCic.context -> NCic.term -> int ->
       NCic.term * NCic.metasenv * NCic.term list

val pack_lc : int * NCic.lc_kind -> int * NCic.lc_kind

val is_out_scope_tag : NCic.meta_attrs -> bool
val int_of_out_scope_tag : NCic.meta_attrs -> int

val is_flexible:
 #NCic.status -> NCic.context -> subst:NCic.substitution -> NCic.term -> bool
