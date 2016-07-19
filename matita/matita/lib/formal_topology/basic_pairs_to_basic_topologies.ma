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

include "formal_topology/basic_pairs_to_o-basic_pairs.ma".
include "formal_topology/o-basic_pairs_to_o-basic_topologies.ma".
include "formal_topology/basic_pairs.ma".
include "formal_topology/basic_topologies.ma".
(*
definition basic_topology_of_basic_pair: basic_pair → basic_topology.
 intro bp;
 letin obt ≝ (OR (BP_to_OBP bp));
 constructor 1;
  [ apply (form bp);
  | apply (oA obt);
  | apply (oJ obt);
  | apply (oA_is_saturation obt);
  | apply (oJ_is_reduction obt);
  | apply (Ocompatibility obt); ]
qed.

definition continuous_relation_of_relation_pair:
 ∀BP1,BP2.relation_pair BP1 BP2 →
  continuous_relation (basic_topology_of_basic_pair BP1) (basic_topology_of_basic_pair BP2).
 intros (BP1 BP2 rp);
 letin ocr ≝ (OR⎽⇒ (BP_to_OBP⎽⇒ rp));
 constructor 1;
  [ apply (rp \sub \f);
  | apply (Oreduced ?? ocr);
  | apply (Osaturated ?? ocr); ]
qed.

alias symbol "compose" (instance 3) = "category1 composition".
alias symbol "compose" (instance 3) = "category1 composition".
record functor1 (C1: category1) (C2: category1) : Type[2] ≝
 { map_objs1:1> C1 → C2;
   map_arrows1: ∀S,T. unary_morphism1 (arrows1 ? S T) (arrows1 ? (map_objs1 S) (map_objs1 T));
   respects_id1: ∀o:C1. map_arrows1 ?? (id1 ? o) =_1 id1 ? (map_objs1 o);
   respects_comp1:
     ∀o1,o2,o3.∀f1:arrows1 ? o1 o2.∀f2:arrows1 ? o2 o3.
     map_arrows1 ?? (f2 ∘ f1) =_1 map_arrows1 ?? f2 ∘ map_arrows1 ?? f1}.

(*
definition BTop_of_BP: functor1 BP BTop.
 constructor 1;
  [ apply basic_topology_of_basic_pair
  | intros; constructor 1 [ apply continuous_relation_of_relation_pair; ]
  | simplify; intro;
  ]
qed.

lemma BBBB_faithful : failthful2 ?? VVV
FIXME
*)
*)
