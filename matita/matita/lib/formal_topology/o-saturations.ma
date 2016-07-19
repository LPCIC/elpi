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

include "formal_topology/o-algebra.ma".
(*
definition is_o_saturation: ∀C:OA. C ⇒_1 C → CProp[1] ≝
 λC:OA.λA:C ⇒_1 C.∀U,V. (U ≤ A V) =_1 (A U ≤ A V).

definition is_o_reduction: ∀C:OA. C ⇒_1 C → CProp[1] ≝
 λC:OA.λJ:C ⇒_1 C.∀U,V. (J U ≤ V) =_1 (J U ≤ J V).

theorem o_saturation_expansive: ∀C,A. is_o_saturation C A → ∀U. U ≤ A U.
 intros; apply (fi ?? (i ??)); apply (oa_leq_refl C).
qed.

theorem o_saturation_monotone: ∀C:OA.∀A:C ⇒_1 C. is_o_saturation C A → ∀U,V. U ≤ V → A U ≤ A V.
 intros; apply (if ?? (i ??)); apply (oa_leq_trans C);
  [apply V|3: apply o_saturation_expansive ]
 assumption.
qed.

theorem o_saturation_idempotent: ∀C:OA.∀A:C ⇒_1 C. is_o_saturation C A → ∀U. A (A U) =_1 A U.
 intros; apply (oa_leq_antisym C);
  [ apply (if ?? (i (A U) U)); apply (oa_leq_refl C).
  | apply o_saturation_expansive; assumption]
qed.
*)
