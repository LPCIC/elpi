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

include "formal_topology/notation.ma".
include "formal_topology/o-basic_pairs.ma".
include "formal_topology/o-basic_topologies.ma".
(*
alias symbol "eq" = "setoid1 eq".

(* Qui, per fare le cose per bene, ci serve la nozione di funtore categorico *)
definition o_basic_topology_of_o_basic_pair: OBP → OBTop.
 intro t;
 constructor 1;
  [ apply (Oform t);
  | apply (□⎽t ∘ Ext⎽t);
  | apply (◊⎽t ∘ Rest⎽t);
  | apply hide; intros 2; split; intro;
     [ change with ((⊩) \sup ⎻* ((⊩) \sup ⎻ U) ≤ (⊩) \sup ⎻* ((⊩) \sup ⎻ V));
       apply (. (#‡(lemma_10_4_a ?? (⊩) V)^-1));
       apply f_minus_star_image_monotone;
       apply f_minus_image_monotone;
       assumption
     | apply oa_leq_trans;
        [3: apply f;
        | skip
        | change with (U ≤ (⊩)⎻* ((⊩)⎻ U));
          apply (. (or_prop2 : ?) ^ -1);
          apply oa_leq_refl; ]]
  | apply hide; intros 2; split; intro;
     [ change with (◊⎽t ((⊩) \sup * U) ≤ ◊⎽t ((⊩) \sup * V));
       apply (. ((lemma_10_4_b ?? (⊩) U)^-1)‡#);
       apply (f_image_monotone ?? (⊩) ? ((⊩)* V));
       apply f_star_image_monotone;
       assumption;
     | apply oa_leq_trans;
        [2: apply f;
        | skip
        | change with ((⊩) ((⊩)* V) ≤ V);
          apply (. (or_prop1 : ?));
          apply oa_leq_refl; ]]
  | apply hide; intros;
    apply (.= (oa_overlap_sym' : ?));
    change with ((◊⎽t ((⊩)* V) >< (⊩)⎻* ((⊩)⎻ U)) = (U >< (◊⎽t ((⊩)* V))));
    apply (.= (or_prop3 ?? (⊩) ((⊩)* V) ?));
    apply (.= #‡(lemma_10_3_a : ?));
    apply (.= (or_prop3 : ?)^-1);
    apply (oa_overlap_sym' ? ((⊩) ((⊩)* V)) U); ]
qed.

definition o_continuous_relation_of_o_relation_pair:
 ∀BP1,BP2.BP1 ⇒_\obp2 BP2 →
  (o_basic_topology_of_o_basic_pair BP1) ⇒_\obt2 (o_basic_topology_of_o_basic_pair BP2).
 intros (BP1 BP2 t);
 constructor 1;
  [ apply (t \sub \f);
  | apply hide; unfold o_basic_topology_of_o_basic_pair; simplify; intros (U e);
    apply sym1;
    apply (.= †(†e)); 
    change in ⊢ (? ? ? (? ? ? ? %) ?) with ((t \sub \f ∘ (⊩)) ((⊩\sub BP1)* U));
    cut ((t \sub \f ∘ (⊩)) ((⊩\sub BP1)* U) = ((⊩) ∘ t \sub \c) ((⊩\sub BP1)* U)) as COM;[2:
      cases (Ocommute ?? t); apply (e3 ^ -1 ((⊩\sub BP1)* U));]
    apply (.= †COM);
    change in ⊢ (? ? ? % ?) with (((⊩) ∘ (⊩)* ) (((⊩) ∘ t \sub \c ∘ (⊩)* ) U));
    apply (.= (lemma_10_3_c ?? (⊩) (t \sub \c ((⊩\sub BP1)* U))));
    apply (.= COM ^ -1);
    change in ⊢ (? ? ? % ?) with (t \sub \f (((⊩) ∘ (⊩\sub BP1)* ) U));
    change in e with (U=((⊩)∘(⊩ \sub BP1) \sup * ) U);
    apply (†e^-1);
  | apply hide; unfold o_basic_topology_of_o_basic_pair; simplify; intros;
    apply sym1;
    apply (.= †(†e));
    change in ⊢ (? ? ? (? ? ? ? %) ?) with ((t \sub \f⎻* ∘ (⊩)⎻* ) ((⊩\sub BP1)⎻ U));
    cut ((t \sub \f⎻* ∘ (⊩)⎻* ) ((⊩\sub BP1)⎻ U) = ((⊩)⎻* ∘ t \sub \c⎻* ) ((⊩\sub BP1)⎻ U)) as COM;[2:
      cases (Ocommute ?? t); apply (e1 ^ -1 ((⊩\sub BP1)⎻ U));]
    apply (.= †COM);
    change in ⊢ (? ? ? % ?) with (((⊩)⎻* ∘ (⊩)⎻ ) (((⊩)⎻* ∘ t \sub \c⎻* ∘ (⊩)⎻ ) U));
    apply (.= (lemma_10_3_d ?? (⊩) (t \sub \c⎻* ((⊩\sub BP1)⎻ U))));
    apply (.= COM ^ -1);
    change in ⊢ (? ? ? % ?) with (t \sub \f⎻* (((⊩)⎻* ∘ (⊩\sub BP1)⎻ ) U));
    change in e with (U=((⊩)⎻* ∘(⊩ \sub BP1)⎻ ) U);
    apply (†e^-1);]
qed.


definition OR : carr3 (OBP ⇒_\c3 OBTop).
constructor 1;
[ apply o_basic_topology_of_o_basic_pair;
| intros; constructor 1;
  [ apply o_continuous_relation_of_o_relation_pair;
  | apply hide; 
    intros; whd; unfold o_continuous_relation_of_o_relation_pair; simplify;;
    change with ((a \sub \f ⎻* ∘ oA (o_basic_topology_of_o_basic_pair S)) =
                 (a' \sub \f ⎻*∘ oA (o_basic_topology_of_o_basic_pair S)));
    whd in e; cases e; clear e e2 e3 e4;
    change in ⊢ (? ? ? (? ? ? ? ? % ?) ?) with ((⊩\sub S)⎻* ∘ (⊩\sub S)⎻);
    apply (.= (comp_assoc2 ? ???? ?? a\sub\f⎻* ));
    change in ⊢ (? ? ? (? ? ? ? ? ? %) ?) with (a\sub\f ∘ ⊩\sub S)⎻*;
    apply (.= #‡†(Ocommute:?)^-1);
    apply (.= #‡e1);
    change in ⊢ (? ? ? (? ? ? ? ? ? %) ?) with (⊩\sub T ∘ a'\sub\c)⎻*;
    apply (.= #‡†(Ocommute:?));    
    change in ⊢ (? ? ? (? ? ? ? ? ? %) ?) with (a'\sub\f⎻* ∘ (⊩\sub S)⎻* );    
    apply (.= (comp_assoc2 ? ???? ?? a'\sub\f⎻* )^-1);
    apply refl2;]
| intros 2 (o a); apply refl1;
| intros 6; apply refl1;]
qed.

*)
