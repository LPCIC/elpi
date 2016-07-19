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

include "formal_topology/basic_topologies.ma".
include "formal_topology/o-basic_topologies.ma".
include "formal_topology/relations_to_o-algebra.ma".
(*
definition o_basic_topology_of_basic_topology: basic_topology → Obasic_topology.
 intros (b); constructor 1;
  [ apply (POW' b) | apply (A b) | apply (J b);
  | apply (A_is_saturation b) | apply (J_is_reduction b) | apply (compatibility b) ]
qed.

definition o_continuous_relation_of_continuous_relation:
 ∀BT1,BT2.continuous_relation BT1 BT2 →
  Ocontinuous_relation (o_basic_topology_of_basic_topology BT1) (o_basic_topology_of_basic_topology BT2).
 intros (BT1 BT2 c); constructor 1;
  [ apply (orelation_of_relation ?? c) | apply (reduced ?? c) | apply (saturated ?? c) ]
qed.

axiom daemon: False.

lemma o_continuous_relation_of_continuous_relation_morphism :
  ∀S,T:category2_of_category1 BTop.
  unary_morphism2 (arrows2 (category2_of_category1 BTop) S T)
   (arrows2 OBTop (o_basic_topology_of_basic_topology S) (o_basic_topology_of_basic_topology T)).
intros (S T);
   constructor 1;
     [ apply (o_continuous_relation_of_continuous_relation S T);
     | cases daemon (*apply (o_relation_pair_of_relation_pair_is_morphism S T)*)]
qed.

definition BTop_to_OBTop: carr3 ((category2_of_category1 BTop) ⇒_\c3 OBTop).
 constructor 1;
  [ apply o_basic_topology_of_basic_topology;
  | intros; apply o_continuous_relation_of_continuous_relation_morphism;
  | cases daemon (*apply o_relation_topology_of_relation_topology_morphism_respects_id*);
  | cases daemon (*apply o_relation_topology_of_relation_topology_morphism_respects_comp*);]
qed.

theorem BTop_to_OBTop_faithful: faithful2 ?? BTop_to_OBTop.
 intros 5; apply (continuous_relation_eq_inv' o1 o2 f g); apply e;
qed.

include "formal_topology/notation.ma".

theorem BTop_to_OBTop_full: full2 ?? BTop_to_OBTop.
 intros 3 (S T);
 cases (POW_full (carrbt S) (carrbt T) (Ocont_rel ?? f)) (g Hg);
 (* cases Hg; *)
 exists [
   constructor 1;
    [ apply g
    | unfold image_coercion; cases daemon (*apply hide; intros; lapply (Oreduced ?? f ? e); unfold image_coercion;
      cases Hg; lapply (e3 U) as K; apply (.= K);
      apply (.= Hletin); apply rule (†(K^-1)); *)
    | cases daemon (* apply hide; intros; lapply (Osaturated ?? f ? e);
      cases Hg; lapply (e1 U) as K; apply (.= K);
      apply (.= Hletin); apply rule (†(K^-1)); *)
    ]
 | simplify; unfold BTop_to_OBTop; simplify;
   cases Hg; unfold o_continuous_relation_of_continuous_relation_morphism;
   simplify;
   change with ((orelation_of_relation ?? g)⎻* ∘ oA (o_basic_topology_of_basic_topology S) =
                f⎻* ∘ oA (o_basic_topology_of_basic_topology S));

   
   change with (g⎻* ∘ oA (o_basic_topology_of_basic_topology S) =
                f⎻* ∘ oA (o_basic_topology_of_basic_topology S));
   apply sym2; whd in T;
   intro;
   apply trans2; [2: apply sym2; [2: apply Hg;
   
   whd in ⊢ (?(??%%)???);
    apply (.= Hg^-1);
   unfold o_continuous_relation_of_continuous_relation_morphism; simplify;
   intro; simplify;
   unfold image_coercion; cases Hg; whd; simplify; intro; simplify;
qed.
*)

