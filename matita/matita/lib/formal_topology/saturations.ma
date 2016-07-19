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

include "formal_topology/relations.ma".
(*
definition is_saturation: ∀C:REL. Ω^C ⇒_1 Ω^C → CProp[1] ≝
 λC:REL.λA:Ω^C ⇒_1 Ω^C. ∀U,V. (U ⊆ A V) =_1 (A U ⊆ A V).

definition is_reduction: ∀C:REL. Ω^C ⇒_1 Ω^C → CProp[1] ≝
 λC:REL.λJ: Ω^C ⇒_1 Ω^C. ∀U,V. (J U ⊆ V) =_1 (J U ⊆ J V).

theorem saturation_expansive: ∀C,A. is_saturation C A → ∀U. U ⊆ A U.
 intros; apply (fi ?? (i ??)); apply subseteq_refl.
qed.

theorem saturation_monotone:
 ∀C,A. is_saturation C A →
  ∀U,V. U ⊆ V → A U ⊆ A V.
 intros; apply (if ?? (i ??)); apply subseteq_trans; [apply V|3: apply saturation_expansive ]
 assumption.
qed.

theorem saturation_idempotent: ∀C,A. is_saturation C A → ∀U. A (A U) = A U.
 intros; split;
  [ apply (if ?? (i ??)); apply subseteq_refl
  | apply saturation_expansive; assumption]
qed.
*)
