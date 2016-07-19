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

include "lambda/paths/standard_precedence.ma".

(* STANDARD ORDER ************************************************************)

(* Note: this is p ≤ q *)
definition sle: relation path ≝ star … sprec.

interpretation "standard 'less or equal to' on paths"
   'leq p q = (sle p q).

lemma sle_step_rc: ∀p,q. p ≺ q → p ≤ q.
/2 width=1/
qed.

lemma sle_step_sn: ∀p1,p,p2. p1 ≺ p → p ≤ p2 → p1 ≤ p2.
/2 width=3/
qed-.

lemma sle_rc: ∀p,q. dx::p ≤ rc::q.
/2 width=1/
qed.

lemma sle_sn: ∀p,q. rc::p ≤ sn::q.
/2 width=1/
qed.

lemma sle_skip: dx::◊ ≤ ◊.
/2 width=1/
qed.

lemma sle_nil: ∀p. ◊ ≤ p.
* // /2 width=1/
qed.

lemma sle_comp: ∀p1,p2. p1 ≤ p2 → ∀o. (o::p1) ≤ (o::p2).
#p1 #p2 #H elim H -p2 // /3 width=3/
qed.

lemma sle_skip_sle: ∀p. p ≤ ◊ → dx::p ≤ ◊.
#p #H @(star_ind_l … p H) -p //
#p #q #Hpq #_ #H @(sle_step_sn … H) -H /2 width=1/
qed.

theorem sle_trans: transitive … sle.
/2 width=3/
qed-.

lemma sle_cons: ∀p,q. dx::p ≤ sn::q.
#p #q
@(sle_trans … (rc::q)) /2 width=1/
qed.

lemma sle_dichotomy: ∀p1,p2:path. p1 ≤ p2 ∨ p2 ≤ p1.
#p1 elim p1 -p1
[ * /2 width=1/
| #o1 #p1 #IHp1 * /2 width=1/
  * #p2 cases o1 -o1 /2 width=1/
  elim (IHp1 p2) -IHp1 /3 width=1/
]
qed-.

lemma sle_inv_dx: ∀p,q. p ≤ q → ∀q0. dx::q0 = q →
                  in_whd p ∨ ∃∃p0. p0 ≤ q0 & dx::p0 = p.
#p #q #H @(star_ind_l … p H) -p [ /3 width=3/ ]
#p0 #p #Hp0 #_ #IHpq #q1 #H destruct
elim (IHpq …) -IHpq [4: // |3: skip ] (**) (* simplify line *)
[ lapply (sprec_fwd_in_whd … Hp0) -Hp0 /3 width=1/
| * #p1 #Hpq1 #H elim (sprec_inv_dx … Hp0 … H) -p
  [ #H destruct /2 width=1/
  | * /4 width=3/
  ]
]
qed-.

lemma sle_inv_rc: ∀p,q. p ≤ q → ∀p0. rc::p0 = p →
                  (∃∃q0. p0 ≤ q0 & rc::q0 = q) ∨
                  ∃q0. sn::q0 = q.
#p #q #H elim H -q /3 width=3/
#q #q0 #_ #Hq0 #IHpq #p0 #H destruct
elim (IHpq p0 …) -IHpq // *
[ #p1 #Hp01 #H
  elim (sprec_inv_rc … Hq0 … H) -q * /3 width=3/ /4 width=3/
| #p1 #H elim (sprec_inv_sn … Hq0 … H) -q /3 width=2/
]
qed-.

lemma sle_inv_sn: ∀p,q. p ≤ q → ∀p0. sn::p0 = p →
                  ∃∃q0. p0 ≤ q0 & sn::q0 = q.
#p #q #H elim H -q /2 width=3/
#q #q0 #_ #Hq0 #IHpq #p0 #H destruct
elim (IHpq p0 …) -IHpq // #p1 #Hp01 #H
elim (sprec_inv_sn … Hq0 … H) -q /3 width=3/
qed-.

lemma in_whd_sle_nil: ∀p. in_whd p → p ≤ ◊.
#p #H @(in_whd_ind … H) -p // /2 width=1/
qed.

theorem in_whd_sle: ∀p. in_whd p → ∀q. p ≤ q.
#p #H @(in_whd_ind … H) -p //
#p #_ #IHp * /3 width=1/ * #q /2 width=1/
qed.

lemma sle_nil_inv_in_whd: ∀p. p ≤ ◊ → in_whd p.
#p #H @(star_ind_l … p H) -p // /2 width=3 by sprec_fwd_in_whd/
qed-.

lemma sle_inv_in_whd: ∀p. (∀q. p ≤ q) → in_whd p.
/2 width=1 by sle_nil_inv_in_whd/
qed-.

lemma sle_fwd_in_whd: ∀p,q. p ≤ q → in_whd q → in_whd p.
#p #q #H @(star_ind_l … p H) -p // /3 width=3 by sprec_fwd_in_whd/
qed-.

lemma sle_fwd_in_inner: ∀p,q. p ≤ q → in_inner p → in_inner q.
/3 width=3 by sle_fwd_in_whd/
qed-.
