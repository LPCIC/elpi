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

include "lambda/terms/multiplicity.ma".

(* SEQUENTIAL REDUCTION (SINGLE STEP) ***************************************)

(* Note: the application "(A B)" is represented by "@B.A" following:
         F. Kamareddine and R.P. Nederpelt: "A useful λ-notation".
         Theoretical Computer Science 155(1), Elsevier (1996), pp. 85-109.
*)
inductive sred: relation term ≝
| sred_beta   : ∀B,A. sred (@B.𝛌.A) ([↙B]A)
| sred_abst   : ∀A1,A2. sred A1 A2 → sred (𝛌.A1) (𝛌.A2) 
| sred_appl_sn: ∀B1,B2,A. sred B1 B2 → sred (@B1.A) (@B2.A)
| sred_appl_dx: ∀B,A1,A2. sred A1 A2 → sred (@B.A1) (@B.A2)
.

interpretation "sequential reduction"
   'SeqRed M N = (sred M N).

lemma sred_inv_vref: ∀M,N. M ↦ N → ∀i. #i = M → ⊥.
#M #N * -M -N
[ #B #A #i #H destruct
| #A1 #A2 #_ #i #H destruct
| #B1 #B2 #A #_ #i #H destruct
| #B #A1 #A2 #_ #i #H destruct
]
qed-.

lemma sred_inv_abst: ∀M,N. M ↦ N → ∀C1. 𝛌.C1 = M →
                     ∃∃C2. C1 ↦ C2 & 𝛌.C2 = N.
#M #N * -M -N
[ #B #A #C1 #H destruct
| #A1 #A2 #HA12 #C1 #H destruct /2 width=3/
| #B1 #B2 #A #_ #C1 #H destruct
| #B #A1 #A2 #_ #C1 #H destruct
]
qed-.

lemma sred_inv_appl: ∀M,N. M ↦ N → ∀D,C. @D.C = M →
                     ∨∨ (∃∃C0.  𝛌.C0 = C & [↙D] C0 = N)
                      | (∃∃D0. D ↦ D0 & @D0.C = N) 
                      | (∃∃C0. C ↦ C0 & @D.C0 = N). 
#M #N * -M -N
[ #B #A #D #C #H destruct /3 width=3/
| #A1 #A2 #_ #D #C #H destruct
| #B1 #B2 #A #HB12 #D #C #H destruct /3 width=3/
| #B #A1 #A2 #HA12 #D #C #H destruct /3 width=3/
]
qed-.

lemma sred_fwd_mult: ∀M,N. M ↦ N → ♯{N} < ♯{M} * ♯{M}.
#M #N #H elim H -M -N
[ #B #A @(le_to_lt_to_lt … (♯{A}*♯{B})) //
  normalize /3 width=1 by lt_minus_to_plus_r, lt_times/ (**) (* auto: too slow without trace *) 
| //
| #B #D #A #_ #IHBD
  @(lt_to_le_to_lt … (♯{B}*♯{B}+♯{A})) [ /2 width=1/ ] -D
| #B #A #C #_ #IHAC
  @(lt_to_le_to_lt … (♯{B}+♯{A}*♯{A})) [ /2 width=1/ ] -C
]
@(transitive_le … (♯{B}*♯{B}+♯{A}*♯{A})) [ /2 width=1/ ]
>distributive_times_plus normalize /2 width=1/
qed-.

lemma sred_lift: liftable sred.
#h #M1 #M2 #H elim H -M1 -M2 normalize /2 width=1/
#B #A #d <dsubst_lift_le //
qed.

lemma sred_inv_lift: deliftable_sn sred.
#h #N1 #N2 #H elim H -N1 -N2
[ #D #C #d #M1 #H
  elim (lift_inv_appl … H) -H #B #M #H0 #HM #H destruct
  elim (lift_inv_abst … HM) -HM #A #H0 #H destruct /3 width=3/
| #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_abst … H) -H #A1 #HAC1 #H
  elim (IHC12 … HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_intro … (𝛌.A2)) // /2 width=1/
| #D1 #D2 #C1 #_ #IHD12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B1 #A #HBD1 #H1 #H2
  elim (IHD12 … HBD1) -D1 #B2 #HB12 #HBD2 destruct
  @(ex2_intro … (@B2.A)) // /2 width=1/
| #D1 #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B #A1 #H1 #HAC1 #H2
  elim (IHC12 … HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_intro … (@B.A2)) // /2 width=1/
]
qed-.

lemma sred_dsubst: dsubstable_dx sred.
#D1 #M1 #M2 #H elim H -M1 -M2 normalize /2 width=1/
#D2 #A #d >dsubst_dsubst_ge //
qed.
