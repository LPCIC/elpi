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

(* $Id: nCicSubstitution.mli 11172 2011-01-11 21:06:37Z sacerdot $ *)

val lift_from : #NCic.status -> ?no_implicit:bool -> int -> int -> NCic.term -> NCic.term 

(* lift n t                                                              *)
(*  lifts [t] of [n]                                                     *)
(*  [from] default 1, lifts only indexes >= [from]                       *)
(*  NOTE: the opposite function (delift_rels) is defined in CicMetaSubst *)
(*  since it needs to restrict the metavariables in case of failure      *)
val lift : #NCic.status -> ?from:int -> ?no_implicit:bool -> int -> NCic.term -> NCic.term

(* subst t1 t2                                                          *)
(*  substitutes [t1] for [Rel 1] in [t2]                                *)
(*  if avoid_beta_redexes is true (default: false) no new beta redexes  *)
(*  are generated. WARNING: the substitution can diverge when t2 is not *)
(*  well typed and avoid_beta_redexes is true.                          *)
val subst : 
  #NCic.status -> ?avoid_beta_redexes:bool -> ?no_implicit:bool -> 
  NCic.term -> NCic.term -> NCic.term

(* psubst [avoid] [map_arg] [args] [t]            
 *  [avoid] : do not leave newly created beta-redexes, default false
 *  [t] : term to fill in
 *  [args] : stuff to substitute
 *  [map_arg] : map the argument to obtain a term
 *    the function is ReductionStrategy.from_env_for_unwind when psubst is
 *    used to implement nCicReduction.unwind'                              *)
val psubst : 
  #NCic.status -> ?avoid_beta_redexes:bool -> ?no_implicit:bool ->
  ('a -> NCic.term) -> 'a list -> NCic.term -> 
    NCic.term

(* subst_meta (n, Ctx [t_1 ; ... ; t_n]) t                                  *)
(*  returns the term [t] where [Rel i] is substituted with [t_i] lifted by n *)
(*  [t_i] is lifted as usual when it crosses an abstraction                  *)
(* subst_meta (n, Irl _) t -> lift n t                                        *)
val subst_meta : #NCic.status -> NCic.local_context -> NCic.term -> NCic.term

