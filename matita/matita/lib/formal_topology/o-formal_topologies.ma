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

include "formal_topology/o-basic_topologies.ma".
(*
(*
(*
definition downarrow: ∀S:BTop. unary_morphism (Ω \sup S) (Ω \sup S).
 intros; constructor 1;
  [ apply (λU:Ω \sup S.{a | ∃b:carrbt S. b ∈ U ∧ a ∈ A ? (singleton ? b)});
    intros; simplify; split; intro; cases H1; cases x; exists [1,3: apply w]
    split; try assumption; [ apply (. H‡#) | apply (. H \sup -1‡#) ] assumption
  | intros; split; intros 2; cases f; exists; [1,3: apply w] cases x; split;
    try assumption; [ apply (. #‡H) | apply (. #‡H \sup -1)] assumption]
qed.

interpretation "downarrow" 'downarrow a = (fun_1 ?? (downarrow ?) a).

definition ffintersects: ∀S:BTop. binary_morphism1 (Ω \sup S) (Ω \sup S) (Ω \sup S).
 intros; constructor 1;
  [ apply (λU,V. ↓U ∩ ↓V);
  | intros; apply (.= (†H)‡(†H1)); apply refl1]
qed.

interpretation "ffintersects" 'fintersects U V = (fun1 ??? (ffintersects ?) U V).
*)

record formal_topology: Type ≝
 { bt:> OBTop;
   converges: ∀U,V: bt. oA bt (U ↓ V) = (oA ? U ∧ oA ? V)
 }.

(*

definition ffintersects': ∀S:BTop. binary_morphism1 S S (Ω \sup S).
 intros; constructor 1;
  [ apply (λb,c:S. (singleton S b) ↓ (singleton S c));
  | intros; apply (.= (†H)‡(†H1)); apply refl1]
qed.

interpretation "ffintersects'" 'fintersects U V = (fun1 ??? (ffintersects' ?) U V).
*)
record formal_map (S,T: formal_topology) : Type ≝
 { cr:> continuous_relation_setoid S T;
   C1: ∀b,c. extS ?? cr (b ↓ c) = ext ?? cr b ↓ ext ?? cr c;
   C2: extS ?? cr T = S
 }.

definition formal_map_setoid: formal_topology → formal_topology → setoid1.
 intros (S T); constructor 1;
  [ apply (formal_map S T);
  | constructor 1;
     [ apply (λf,f1: formal_map S T.f=f1);
     | simplify; intros 1; apply refl1
     | simplify; intros 2; apply sym1
     | simplify; intros 3; apply trans1]]
qed.

axiom C1':
 ∀S,T: formal_topology.∀f:formal_map_setoid S T.∀U,V: Ω \sup T.
  extS ?? f (U ↓ V) = extS ?? f U ↓ extS ?? f V.

definition formal_map_composition:
 ∀o1,o2,o3: formal_topology.
  binary_morphism1
   (formal_map_setoid o1 o2)
   (formal_map_setoid o2 o3)
   (formal_map_setoid o1 o3).
 intros; constructor 1;
  [ intros; whd in c c1; constructor 1;
     [ apply (comp1 BTop ??? c c1);
     | intros;
       apply (.= (extS_com ??? c c1 ?));
       apply (.= †(C1 ?????));
       apply (.= (C1' ?????));
       apply (.= ((†((extS_singleton ????) \sup -1))‡(†((extS_singleton ????) \sup -1))));
       apply (.= (extS_com ??????)\sup -1 ‡ (extS_com ??????) \sup -1);
       apply (.= (extS_singleton ????)‡(extS_singleton ????));
       apply refl1;
     | apply (.= (extS_com ??? c c1 ?));
       apply (.= (†(C2 ???)));
       apply (.= (C2 ???));
       apply refl1;]
  | intros; simplify;
    change with (comp1 BTop ??? a b = comp1 BTop ??? a' b');
    apply prop1; assumption]
qed.
*)
*)
