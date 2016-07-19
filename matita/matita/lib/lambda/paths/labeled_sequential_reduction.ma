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
include "lambda/terms/sequential_reduction.ma".

(* PATH-LABELED SEQUENTIAL REDUCTION (SINGLE STEP) **************************)

inductive pl_sred: path → relation term ≝
| pl_sred_beta   : ∀B,A. pl_sred (◊) (@B.𝛌.A) ([↙B]A)
| pl_sred_abst   : ∀p,A1,A2. pl_sred p A1 A2 → pl_sred (rc::p) (𝛌.A1) (𝛌.A2) 
| pl_sred_appl_sn: ∀p,B1,B2,A. pl_sred p B1 B2 → pl_sred (sn::p) (@B1.A) (@B2.A)
| pl_sred_appl_dx: ∀p,B,A1,A2. pl_sred p A1 A2 → pl_sred (dx::p) (@B.A1) (@B.A2)
.

interpretation "path-labeled sequential reduction"
   'SeqRed M p N = (pl_sred p M N).

lemma sred_pl_sred: ∀M,N. M ↦ N → ∃p. M ↦[p] N.
#M #N #H elim H -M -N
[ /2 width=2/
| #A1 #A2 #_ * /3 width=2/
| #B1 #B2 #A #_ * /3 width=2/
| #B #A1 #A2 #_ * /3 width=2/
]
qed-.

lemma pl_sred_inv_sred: ∀p,M,N. M ↦[p] N → M ↦ N.
#p #M #N #H elim H -p -M -N // /2 width=1/
qed-.

lemma pl_sred_inv_vref: ∀p,M,N. M ↦[p] N → ∀i. #i = M → ⊥.
/3 width=5 by pl_sred_inv_sred, sred_inv_vref/
qed-.

lemma pl_sred_inv_nil: ∀p,M,N. M ↦[p] N → ◊ = p →
                       ∃∃B,A. @B. 𝛌.A = M & [↙B] A = N.
#p #M #N * -p -M -N
[ #B #A #_ destruct /2 width=4/
| #p #A1 #A2 #_ #H destruct
| #p #B1 #B2 #A #_ #H destruct
| #p #B #A1 #A2 #_ #H destruct
]
qed-.

lemma pl_sred_inv_rc: ∀p,M,N. M ↦[p] N → ∀q. rc::q = p →
                      ∃∃A1,A2. A1 ↦[q] A2 & 𝛌.A1 = M & 𝛌.A2 = N.
#p #M #N * -p -M -N
[ #B #A #q #H destruct
| #p #A1 #A2 #HA12 #q #H destruct /2 width=5/
| #p #B1 #B2 #A #_ #q #H destruct
| #p #B #A1 #A2 #_ #q #H destruct
]
qed-.

lemma pl_sred_inv_sn: ∀p,M,N. M ↦[p] N → ∀q. sn::q = p →
                      ∃∃B1,B2,A. B1 ↦[q] B2 & @B1.A = M & @B2.A = N.
#p #M #N * -p -M -N
[ #B #A #q #H destruct
| #p #A1 #A2 #_ #q #H destruct
| #p #B1 #B2 #A #HB12 #q #H destruct /2 width=6/
| #p #B #A1 #A2 #_ #q #H destruct
]
qed-.

lemma pl_sred_inv_dx: ∀p,M,N. M ↦[p] N → ∀q. dx::q = p →
                      ∃∃B,A1,A2. A1 ↦[q] A2 & @B.A1 = M & @B.A2 = N.
#p #M #N * -p -M -N
[ #B #A #q #H destruct
| #p #A1 #A2 #_ #q #H destruct
| #p #B1 #B2 #A #_ #q #H destruct
| #p #B #A1 #A2 #HA12 #q #H destruct /2 width=6/
]
qed-.

lemma pl_sred_lift: ∀p. liftable (pl_sred p).
#p #h #M1 #M2 #H elim H -p -M1 -M2 normalize /2 width=1/
#B #A #d <dsubst_lift_le //
qed.

lemma pl_sred_inv_lift: ∀p. deliftable_sn (pl_sred p).
#p #h #N1 #N2 #H elim H -p -N1 -N2
[ #D #C #d #M1 #H
  elim (lift_inv_appl … H) -H #B #M #H0 #HM #H destruct
  elim (lift_inv_abst … HM) -HM #A #H0 #H destruct /3 width=3/
| #p #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_abst … H) -H #A1 #HAC1 #H
  elim (IHC12 … HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_intro … (𝛌.A2)) // /2 width=1/
| #p #D1 #D2 #C1 #_ #IHD12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B1 #A #HBD1 #H1 #H2
  elim (IHD12 … HBD1) -D1 #B2 #HB12 #HBD2 destruct
  @(ex2_intro … (@B2.A)) // /2 width=1/
| #p #D1 #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B #A1 #H1 #HAC1 #H2
  elim (IHC12 … HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_intro … (@B.A2)) // /2 width=1/
]
qed-.

lemma pl_sred_dsubst: ∀p. dsubstable_dx (pl_sred p).
#p #D1 #M1 #M2 #H elim H -p -M1 -M2 normalize /2 width=1/
#D2 #A #d >dsubst_dsubst_ge //
qed.

theorem pl_sred_mono: ∀p. singlevalued … (pl_sred p).
#p #M #N1 #H elim H -p -M -N1
[ #B #A #N2 #H elim (pl_sred_inv_nil … H …) -H //
  #D #C #H #HN2 destruct //
| #p #A1 #A2 #_ #IHA12 #N2 #H elim (pl_sred_inv_rc … H …) -H [3: // |2: skip ] (**) (* simplify line *)
  #C1 #C2 #HC12 #H #HN2 destruct /3 width=1/
| #p #B1 #B2 #A #_ #IHB12 #N2 #H elim (pl_sred_inv_sn … H …) -H [3: // |2: skip ] (**) (* simplify line *)
  #D1 #D2 #C #HD12 #H #HN2 destruct /3 width=1/
| #p #B #A1 #A2 #_ #IHA12 #N2 #H elim (pl_sred_inv_dx … H …) -H [3: // |2: skip ] (**) (* simplify line *)
  #D #C1 #C2 #HC12 #H #HN2 destruct /3 width=1/
]
qed-.
