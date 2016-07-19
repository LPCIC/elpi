(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "formal_topology/concrete_spaces.ma".
include "formal_topology/o-concrete_spaces.ma".
include "formal_topology/basic_pairs_to_o-basic_pairs.ma".
(*
(*
(* Qui, per fare le cose per bene, ci serve la nozione di funtore categorico *)
definition o_concrete_space_of_concrete_space: cic:/matita/formal_topology/concrete_spaces/concrete_space.ind#xpointer(1/1) → concrete_space.
 intro;
 constructor 1;
  [ apply (o_basic_pair_of_basic_pair (bp c));
  | lapply depth=0 (downarrow c);
    constructor 1;
     [ apply 
     |
    apply (o_operator_of_operator);fintersectsS);
  |
  |
  |
  |
  |
  ]
qed.

definition o_convergent_relation_pair_of_convergent_relation_pair:
 ∀BP1,BP2.cic:/matita/formal_topology/concrete_spaces/convergent_relation_pair.ind#xpointer(1/1) BP1 BP2 →
  convergent_relation_pair (o_concrete_space_of_concrete_space BP1) (o_concrete_space_of_concrete_space BP2).
 intros;
 constructor 1;
  [ apply (orelation_of_relation ?? (r \sub \c));
  | apply (orelation_of_relation ?? (r \sub \f));
  | lapply (commute ?? r);
    lapply (orelation_of_relation_preserves_equality ???? Hletin);
    apply (.= (orelation_of_relation_preserves_composition (concr BP1) ??? (rel BP2)) ^ -1);
    apply (.= (orelation_of_relation_preserves_equality ???? (commute ?? r)));
    apply (orelation_of_relation_preserves_composition ?? (form BP2)  (rel BP1) ?); ]
qed.

*)
*)
