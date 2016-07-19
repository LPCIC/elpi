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

include "lambda/terms/parallel_reduction.ma".

(* PARALLEL COMPUTATION (MULTISTEP) *****************************************)

definition preds: relation term ≝ star … pred.

interpretation "parallel computation"
   'ParRedStar M N = (preds M N).

lemma preds_refl: reflexive … preds.
//
qed.

lemma preds_step_sn: ∀M1,M. M1 ⤇ M → ∀M2. M ⤇* M2 → M1 ⤇* M2.
/2 width=3/
qed-.

lemma preds_step_dx: ∀M1,M. M1 ⤇* M → ∀M2. M ⤇ M2 → M1 ⤇* M2.
/2 width=3/
qed-.

lemma preds_step_rc: ∀M1,M2. M1 ⤇ M2 → M1 ⤇* M2.
/2 width=1/
qed.

lemma preds_compatible_abst: compatible_abst preds.
/3 width=1/
qed.

lemma preds_compatible_sn: compatible_sn preds.
/3 width=1/
qed.

lemma preds_compatible_dx: compatible_dx preds.
/3 width=1/
qed.

lemma preds_compatible_appl: compatible_appl preds.
/3 width=1/
qed.

lemma preds_lift: liftable preds.
/2 width=1/
qed.

lemma preds_inv_lift: deliftable_sn preds.
/3 width=3 by star_deliftable_sn, pred_inv_lift/
qed-.

lemma preds_dsubst_dx: dsubstable_dx preds.
/2 width=1/
qed.

lemma preds_dsubst: dsubstable preds.
/2 width=1/
qed.

theorem preds_trans: transitive … preds.
/2 width=3 by trans_star/
qed-.

lemma preds_strip: ∀M0,M1. M0 ⤇* M1 → ∀M2. M0 ⤇ M2 →
                   ∃∃M. M1 ⤇ M & M2 ⤇* M.
/3 width=3 by star_strip, pred_conf/
qed-.

theorem preds_conf: confluent … preds.
/3 width=3 by star_confluent, pred_conf/
qed-.
