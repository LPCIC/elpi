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

include "lambda/paths/trace.ma".
include "lambda/paths/standard_order.ma".

(* STANDARD TRACE ***********************************************************)

(* Note: to us, a "standard" computation contracts redexes in non-decreasing positions *)
definition is_standard: predicate trace ≝ Allr … sle.

lemma is_standard_fwd_append_sn: ∀s,r. is_standard (s@r) → is_standard s.
/2 width=2 by Allr_fwd_append_sn/
qed-.

lemma is_standard_fwd_cons: ∀p,s. is_standard (p::s) → is_standard s.
/2 width=2 by Allr_fwd_cons/
qed-.

lemma is_standard_fwd_append_dx: ∀s,r. is_standard (s@r) → is_standard r.
/2 width=2 by Allr_fwd_append_dx/
qed-.

lemma is_standard_compatible: ∀o,s. is_standard s → is_standard (o:::s).
#o #s elim s -s // #p * //
#q #s #IHs * /3 width=1/
qed.

lemma is_standard_cons: ∀p,s. is_standard s → is_standard ((dx::p)::sn:::s).
#p #s elim s -s // #q1 * /2 width=1/
#q2 #s #IHs * /4 width=1/
qed.

lemma is_standard_append: ∀r. is_standard r → ∀s. is_standard s → is_standard ((dx:::r)@sn:::s).
#r elim r -r /3 width=1/ #p * /2 width=1/
#q #r #IHr * /3 width=1/
qed.

lemma is_standard_inv_compatible_sn: ∀s. is_standard (sn:::s) → is_standard s.
#s elim s -s // #a1 * // #a2 #s #IHs * #H
elim (sle_inv_sn … H …) -H [3: // |2: skip ] (**) (* simplify line *)
#a #Ha1 #H destruct /3 width=1/
qed-.

lemma is_standard_inv_compatible_rc: ∀s. is_standard (rc:::s) → is_standard s.
#s elim s -s // #a1 * // #a2 #s #IHs * #H
elim (sle_inv_rc … H …) -H [4: // |2: skip ] * (**) (* simplify line *)
[ #a #Ha1 #H destruct /3 width=1/
| #a #H destruct
]
qed-.

lemma is_standard_inv_compatible_dx: ∀s. is_standard (dx:::s) →
                                     is_inner s → is_standard s.
#s elim s -s // #a1 * // #a2 #s #IHs * #H
elim (sle_inv_dx … H …) -H [4: // |3: skip ] (**) (* simplify line *)
[ * #_ #H1a1 #_ * #H2a1 #_ -IHs
  elim (H2a1 …) -H2a1 -a2 -s //
| * #a #Ha2 #H destruct #H * #_ /3 width=1/
qed-.

lemma is_standard_fwd_sle: ∀s2,p2,s1,p1. is_standard ((p1::s1)@(p2::s2)) → p1 ≤ p2.
#s2 #p2 #s1 elim s1 -s1
[ #p1 * //
| #q1 #s1 #IHs1 #p1 * /3 width=3 by sle_trans/
]
qed-.

lemma is_standard_in_whd: ∀p. in_whd p → ∀s. is_standard s → is_standard (p::s).
#p #Hp * // /3 width=1/
qed.

theorem is_whd_is_standard: ∀s. is_whd s → is_standard s.
#s elim s -s // #p * //
#q #s #IHs * /3 width=1/
qed.

theorem is_whd_is_standard_trans: ∀r. is_whd r → ∀s. is_standard s → is_standard (r@s).
#r elim r -r // #p *
[ #_ * /2 width=1/
| #q #r #IHr * /3 width=1/
]
qed.

lemma is_standard_fwd_is_whd: ∀s,p,r. in_whd p → is_standard (r@(p::s)) → is_whd r.
#s #p #r elim r -r // #q #r #IHr #Hp #H
lapply (is_standard_fwd_cons … H)
lapply (is_standard_fwd_sle … H) #Hqp
lapply (sle_fwd_in_whd … Hqp Hp) /3 width=1/
qed-.

lemma is_standard_fwd_in_inner: ∀s,p. is_standard (p::s) → in_inner p → is_inner s.
#s elim s -s // #q #s #IHs #p * #Hpq #Hs #Hp
lapply (sle_fwd_in_inner … Hpq ?) // -p /3 width=3/
qed.
