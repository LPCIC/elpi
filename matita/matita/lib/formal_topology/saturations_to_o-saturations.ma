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

include "formal_topology/saturations.ma".
include "formal_topology/o-saturations.ma".
include "formal_topology/relations_to_o-algebra.ma".
(*
(* These are only conversions :-) *)

definition o_operator_of_operator: ∀C:REL. (Ω^C ⇒_1 Ω^C) → ((POW C) ⇒_1 (POW C)) ≝ λC,t.t.

definition is_o_saturation_of_is_saturation: 
  ∀C:REL.∀R: Ω^C ⇒_1 Ω^C. is_saturation ? R → is_o_saturation ? (o_operator_of_operator ? R).
intros (C R i); apply i; qed.

definition is_o_reduction_of_is_reduction: 
  ∀C:REL.∀R: Ω^C ⇒_1 Ω^C.is_reduction ? R → is_o_reduction ? (o_operator_of_operator ? R).
intros (C R i); apply i; qed.
*)
