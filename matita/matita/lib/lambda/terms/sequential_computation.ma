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

include "lambda/terms/parallel_computation.ma".

(* SEQUENTIAL COMPUTATION (MULTISTEP) ***************************************)

definition sreds: relation term ≝ star … sred.

interpretation "sequential computation"
   'SeqRedStar M N = (sreds M N).

lemma sreds_refl: reflexive … sreds.
//
qed.

lemma sreds_step_sn: ∀M1,M. M1 ↦ M → ∀M2. M ↦* M2 → M1 ↦* M2.
/2 width=3/
qed-.

lemma sreds_step_dx: ∀M1,M. M1 ↦* M → ∀M2. M ↦ M2 → M1 ↦* M2.
/2 width=3/
qed-.

lemma sreds_step_rc: ∀M1,M2. M1 ↦ M2 → M1 ↦* M2.
/2 width=1/
qed.

lemma lsred_compatible_abst: compatible_abst sreds.
/3 width=1/
qed.

lemma sreds_compatible_sn: compatible_sn sreds.
/3 width=1/
qed.

lemma sreds_compatible_dx: compatible_dx sreds.
/3 width=1/
qed.

lemma sreds_compatible_appl: compatible_appl sreds.
/3 width=3/
qed.

lemma sreds_lift: liftable sreds.
/2 width=1/
qed.

lemma sreds_inv_lift: deliftable_sn sreds.
/3 width=3 by star_deliftable_sn, sred_inv_lift/
qed-.

lemma sreds_dsubst: dsubstable_dx sreds.
/2 width=1/
qed.

theorem sreds_trans: transitive … sreds.
/2 width=3 by trans_star/
qed-.

(* Note: the substitution should be unparentesized *) 
lemma sreds_compatible_beta: ∀B1,B2. B1 ↦* B2 → ∀A1,A2. A1 ↦* A2 →
                             @B1.𝛌.A1 ↦* ([↙B2] A2).
#B1 #B2 #HB12 #A1 #A2 #HA12
@(sreds_trans … (@B2.𝛌.A1)) /2 width=1/ -B1
@(sreds_step_dx … (@B2.𝛌.A2)) // /3 width=1/
qed.

theorem sreds_preds: ∀M1,M2. M1 ↦* M2 → M1 ⤇* M2.
#M1 #M2 #H @(star_ind_l … M1 H) -M1 //
#M1 #M #HM1 #_ #IHM2
@(preds_step_sn … IHM2) -M2 /2 width=2/
qed.

lemma pred_sreds: ∀M1,M2. M1 ⤇ M2 → M1 ↦* M2.
#M1 #M2 #H elim H -M1 -M2 // /2 width=1/
qed-.

theorem preds_sreds: ∀M1,M2. M1 ⤇* M2 → M1 ↦* M2.
#M1 #M2 #H elim H -M2 //
#M #M2 #_ #HM2 #HM1
lapply (pred_sreds … HM2) -HM2 #HM2
@(sreds_trans … HM1 … HM2)
qed-.

theorem sreds_conf: ∀M0,M1. M0 ↦* M1 → ∀M2. M0 ↦* M2 →
                    ∃∃M. M1 ↦* M & M2 ↦* M.
#M0 #M1 #HM01 #M2 #HM02
lapply (sreds_preds … HM01) #HM01
lapply (sreds_preds … HM02) #HM02
elim (preds_conf … HM01 … HM02) -M0 #M #HM1 #HM2
lapply (preds_sreds … HM1) -HM1
lapply (preds_sreds … HM2) -HM2 /2 width=3/
qed-.
