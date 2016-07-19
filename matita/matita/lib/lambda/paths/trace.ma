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

include "lambda/paths/path.ma".

(* TRACE ********************************************************************)

(* Policy: trace metavariables: r, s *)
definition trace: Type[0] ≝ list path.

definition ho_compatible_rc: predicate (trace→relation term) ≝ λR.
                             ∀s,A1,A2. R s A1 A2 → R (rc:::s) (𝛌.A1) (𝛌.A2).

definition ho_compatible_sn: predicate (trace→relation term) ≝ λR.
                             ∀s,B1,B2,A. R s B1 B2 → R (sn:::s) (@B1.A) (@B2.A).

definition ho_compatible_dx: predicate (trace→relation term) ≝ λR.
                             ∀s,B,A1,A2. R s A1 A2 → R (dx:::s) (@B.A1) (@B.A2).

lemma lstar_compatible_rc: ∀R. compatible_rc R → ho_compatible_rc (lstar … R).
#R #HR #s #A1 #A2 #H @(lstar_ind_l … s A1 H) -s -A1 // /3 width=3/
qed.

lemma lstar_compatible_sn: ∀R. compatible_sn R → ho_compatible_sn (lstar … R).
#R #HR #s #B1 #B2 #A #H @(lstar_ind_l … s B1 H) -s -B1 // /3 width=3/
qed.

lemma lstar_compatible_dx: ∀R. compatible_dx R → ho_compatible_dx (lstar … R).
#R #HR #s #B #A1 #A2 #H @(lstar_ind_l … s A1 H) -s -A1 // /3 width=3/
qed.

(* Note: a "whd" computation contracts just redexes in the whd *)
definition is_whd: predicate trace ≝ All … in_whd.

lemma is_whd_dx: ∀s. is_whd s → is_whd (dx:::s).
#s elim s -s //
#p #s #IHs * /3 width=1/
qed.

lemma is_whd_append: ∀r. is_whd r → ∀s. is_whd s → is_whd (r@s).
/2 width=1 by All_append/
qed.

lemma is_whd_inv_dx: ∀s. is_whd (dx:::s) → is_whd s.
#s elim s -s //
#p #s #IHs * * #_ /3 width=1/
qed-.

lemma is_whd_inv_append: ∀r,s. is_whd (r@s) → is_whd r ∧ is_whd s.
/2 width=1 by All_inv_append/
qed-.

(* Note: an "inner" computation contracts just redexes not in the whd *)
definition is_inner: predicate trace ≝ All … in_inner.

lemma is_inner_append: ∀r. is_inner r → ∀s. is_inner s → is_inner (r@s).
/2 width=1 by All_append/
qed.

lemma is_whd_is_inner_inv: ∀s. is_whd s → is_inner s → ◊ = s.
* // #p #s * #H1p #_ * #H2p #_ elim (H2p …) -H2p //
qed-.
