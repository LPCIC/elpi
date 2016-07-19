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

include "lambda/terms/labeled_sequential_computation.ma".
include "lambda/paths/trace.ma".
include "lambda/paths/labeled_sequential_reduction.ma".

(* PATH-LABELED SEQUENTIAL COMPUTATION (MULTISTEP) *******************************)

(* Note: lstar shuld be replaced by l_sreds *)
definition pl_sreds: trace → relation term ≝ lstar … pl_sred.

interpretation "path-labeled sequential computation"
   'SeqRedStar M s N = (pl_sreds s M N).

lemma sreds_pl_sreds: ∀M,N. M ↦* N → ∃s. M ↦*[s] N.
/3 width=1 by sreds_l_sreds, sred_pl_sred/
qed-.

lemma pl_sreds_inv_sreds: ∀s,M,N. M ↦*[s] N → M ↦* N.
/3 width=5 by l_sreds_inv_sreds, pl_sred_inv_sred/
qed-.

lemma pl_sreds_refl: reflexive … (pl_sreds (◊)).
//
qed.

lemma pl_sreds_step_sn: ∀p,M1,M. M1 ↦[p] M → ∀s,M2. M ↦*[s] M2 → M1 ↦*[p::s] M2.
/2 width=3/
qed-.

lemma pl_sreds_step_dx: ∀s,M1,M. M1 ↦*[s] M → ∀p,M2. M ↦[p] M2 → M1 ↦*[s@p::◊] M2.
/2 width=3/
qed-.

lemma pl_sreds_step_rc: ∀p,M1,M2. M1 ↦[p] M2 → M1 ↦*[p::◊] M2.
/2 width=1/
qed.

lemma pl_sreds_inv_nil: ∀s,M1,M2. M1 ↦*[s] M2 → ◊ = s → M1 = M2.
/2 width=5 by lstar_inv_nil/
qed-.

lemma pl_sreds_inv_cons: ∀s,M1,M2. M1 ↦*[s] M2 → ∀q,r. q::r = s →
                         ∃∃M. M1 ↦[q] M & M ↦*[r] M2.
/2 width=3 by lstar_inv_cons/
qed-.

lemma pl_sreds_inv_step_rc: ∀p,M1,M2. M1 ↦*[p::◊] M2 → M1 ↦[p] M2.
/2 width=1 by lstar_inv_step/
qed-.

lemma pl_sreds_inv_pos: ∀s,M1,M2. M1 ↦*[s] M2 → 0 < |s| →
                        ∃∃p,r,M. p::r = s & M1 ↦[p] M & M ↦*[r] M2.
/2 width=1 by lstar_inv_pos/
qed-.

lemma lsred_compatible_rc: ho_compatible_rc pl_sreds.
/3 width=1/
qed.

lemma pl_sreds_compatible_sn: ho_compatible_sn pl_sreds.
/3 width=1/
qed.

lemma pl_sreds_compatible_dx: ho_compatible_dx pl_sreds.
/3 width=1/
qed.

lemma pl_sreds_lift: ∀s. liftable (pl_sreds s).
/2 width=1/
qed.

lemma pl_sreds_inv_lift: ∀s. deliftable_sn (pl_sreds s).
/3 width=3 by lstar_deliftable_sn, pl_sred_inv_lift/
qed-.

lemma pl_sreds_dsubst: ∀s. dsubstable_dx (pl_sreds s).
/2 width=1/
qed.

theorem pl_sreds_mono: ∀s. singlevalued … (pl_sreds s).
/3 width=7 by lstar_singlevalued, pl_sred_mono/
qed-.

theorem pl_sreds_trans: ltransitive … pl_sreds.
/2 width=3 by lstar_ltransitive/
qed-.

lemma pl_sreds_compatible_appl: ∀r,B1,B2. B1 ↦*[r] B2 → ∀s,A1,A2. A1 ↦*[s] A2 →
                                @B1.A1 ↦*[(sn:::r)@dx:::s] @B2.A2.
#r #B1 #B2 #HB12 #s #A1 #A2 #HA12
@(pl_sreds_trans … (@B2.A1)) /2 width=1/
qed.

lemma pl_sreds_compatible_beta: ∀r,B1,B2. B1 ↦*[r] B2 → ∀s,A1,A2. A1 ↦*[s] A2 →
                                @B1.𝛌.A1 ↦*[(sn:::r)@(dx:::rc:::s)@◊::◊] [↙B2] A2.
#r #B1 #B2 #HB12 #s #A1 #A2 #HA12
@(pl_sreds_trans … (@B2.𝛌.A1)) /2 width=1/ -r -B1
@(pl_sreds_step_dx … (@B2.𝛌.A2)) // /3 width=1/
qed.
