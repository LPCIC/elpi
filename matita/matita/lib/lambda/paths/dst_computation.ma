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

include "lambda/paths/standard_trace.ma".
include "lambda/paths/labeled_sequential_computation.ma".

(* DECOMPOSED STANDARD COMPUTATION ***********************************************)

(* Note: this is the "standard" computation of:
         R. Kashima: "A proof of the Standization Theorem in λ-Calculus". (2000).
*)
inductive dst: relation term ≝
| dst_vref: ∀s,M,i. is_whd s → M ↦*[s] #i → dst M (#i)
| dst_abst: ∀s,M,A1,A2. is_whd s → M ↦*[s] 𝛌.A1 → dst A1 A2 → dst M (𝛌.A2)
| dst_appl: ∀s,M,B1,B2,A1,A2. is_whd s → M ↦*[s] @B1.A1 → dst B1 B2 → dst A1 A2 → dst M (@B2.A2)
.

interpretation "decomposed standard computation"
    'DecomposedStd M N = (dst M N).

notation "hvbox( M break ⓢ↦* term 46 N )"
   non associative with precedence 45
   for @{ 'DecomposedStd $M $N }.

lemma dst_inv_lref: ∀M,N. M ⓢ↦* N → ∀j. #j = N →
                    ∃∃s. is_whd s & M ↦*[s] #j.
#M #N * -M -N
[ /2 width=3/
| #s #M #A1 #A2 #_ #_ #_ #j #H destruct
| #s #M #B1 #B2 #A1 #A2 #_ #_ #_ #_ #j #H destruct
]
qed-.

lemma dst_inv_abst: ∀M,N. M ⓢ↦* N → ∀C2. 𝛌.C2 = N →
                    ∃∃s,C1. is_whd s & M ↦*[s] 𝛌.C1 & C1 ⓢ↦* C2.
#M #N * -M -N
[ #s #M #i #_ #_ #C2 #H destruct
| #s #M #A1 #A2 #Hs #HM #A12 #C2 #H destruct /2 width=5/
| #s #M #B1 #B2 #A1 #A2 #_ #_ #_ #_ #C2 #H destruct
]
qed-.

lemma dst_inv_appl: ∀M,N. M ⓢ↦* N → ∀D2,C2. @D2.C2 = N →
                    ∃∃s,D1,C1. is_whd s & M ↦*[s] @D1.C1 & D1 ⓢ↦* D2 & C1 ⓢ↦* C2.
#M #N * -M -N
[ #s #M #i #_ #_ #D2 #C2 #H destruct
| #s #M #A1 #A2 #_ #_ #_ #D2 #C2 #H destruct
| #s #M #B1 #B2 #A1 #A2 #Hs #HM #HB12 #HA12 #D2 #C2 #H destruct /2 width=7/
]
qed-.

lemma dst_refl: reflexive … dst.
#M elim M -M /2 width=3/ /2 width=5/ /2 width=7/
qed.

lemma dst_step_sn: ∀N1,N2. N1 ⓢ↦* N2 → ∀s,M. is_whd s → M ↦*[s] N1 → M ⓢ↦* N2.
#N1 #N2 #H elim H -N1 -N2
[ #r #N #i #Hr #HN #s #M #Hs #HMN
  lapply (pl_sreds_trans … HMN … HN) -N /3 width=3/
| #r #N #C1 #C2 #Hr #HN #_ #IHC12 #s #M #Hs #HMN
  lapply (pl_sreds_trans … HMN … HN) -N /3 width=7/
| #r #N #D1 #D2 #C1 #C2 #Hr #HN #_ #_ #IHD12 #IHC12 #s #M #Hs #HMN
  lapply (pl_sreds_trans … HMN … HN) -N /3 width=9/
]
qed-.

lemma dst_step_rc: ∀s,M1,M2. is_whd s → M1 ↦*[s] M2 → M1 ⓢ↦* M2.
/3 width=5 by dst_step_sn/
qed.

lemma dst_lift: liftable dst.
#h #M1 #M2 #H elim H -M1 -M2
[ /3 width=3/
| #s #M #A1 #A2 #Hs #HM #_ #IHA12 #d
  @(dst_abst … Hs) [2: @(pl_sreds_lift … HM) | skip ] -M // (**) (* auto fails here *)
| #s #M #B1 #B2 #A1 #A2 #Hs #HM #_ #_ #IHB12 #IHA12 #d
  @(dst_appl … Hs) [3: @(pl_sreds_lift … HM) |1,2: skip ] -M // (**) (* auto fails here *)
]
qed.

lemma dst_inv_lift: deliftable_sn dst.
#h #N1 #N2 #H elim H -N1 -N2
[ #s #N1 #i #Hs #HN1 #d #M1 #HMN1
  elim (pl_sreds_inv_lift … HN1 … HMN1) -N1 /3 width=3/
| #s #N1 #C1 #C2 #Hs  #HN1 #_ #IHC12 #d #M1 #HMN1
  elim (pl_sreds_inv_lift … HN1 … HMN1) -N1 #M2 #HM12 #HM2
  elim (lift_inv_abst … HM2) -HM2 #A1 #HAC1 #HM2 destruct
  elim (IHC12 …) -IHC12 [4: // |2,3: skip ] #A2 #HA12 #HAC2 destruct (**) (* simplify line *)
  @(ex2_intro … (𝛌.A2)) // /2 width=5/
| #s #N1 #D1 #D2 #C1 #C2 #Hs #HN1 #_ #_ #IHD12 #IHC12 #d #M1 #HMN1
  elim (pl_sreds_inv_lift … HN1 … HMN1) -N1 #M2 #HM12 #HM2
  elim (lift_inv_appl … HM2) -HM2 #B1 #A1 #HBD1 #HAC1 #HM2 destruct
  elim (IHD12 …) -IHD12 [4: // |2,3: skip ] #B2 #HB12 #HBD2 destruct (**) (* simplify line *)
  elim (IHC12 …) -IHC12 [4: // |2,3: skip ] #A2 #HA12 #HAC2 destruct (**) (* simplify line *)
  @(ex2_intro … (@B2.A2)) // /2 width=7/
]
qed-.

lemma dst_dsubst: dsubstable dst.
#N1 #N2 #HN12 #M1 #M2 #H elim H -M1 -M2
[ #s #M #i #Hs #HM #d elim (lt_or_eq_or_gt i d) #Hid
  [ lapply (pl_sreds_dsubst … N1 … HM d) -HM
    >(dsubst_vref_lt … Hid) >(dsubst_vref_lt … Hid) /2 width=3/
  | destruct >dsubst_vref_eq
    @(dst_step_sn (↑[0,i]N1) … s) /2 width=1/
  | lapply (pl_sreds_dsubst … N1 … HM d) -HM
    >(dsubst_vref_gt … Hid) >(dsubst_vref_gt … Hid) /2 width=3/
  ]
| #s #M #A1 #A2 #Hs #HM #_ #IHA12 #d
  lapply (pl_sreds_dsubst … N1 … HM d) -HM /2 width=5/ (**) (* auto needs some help here *)
| #s #M #B1 #B2 #A1 #A2 #Hs #HM #_ #_ #IHB12 #IHA12 #d
  lapply (pl_sreds_dsubst … N1 … HM d) -HM /2 width=7/ (**) (* auto needs some help here *)
]
qed.

lemma dst_step_dx: ∀p,M,M2. M ↦[p] M2 → ∀M1. M1 ⓢ↦* M → M1 ⓢ↦* M2.
#p #M #M2 #H elim H -p -M -M2
[ #B #A #M1 #H
  elim (dst_inv_appl … H …) -H [4: // |2,3: skip ] #s #B1 #M #Hs #HM1 #HB1 #H (**) (* simplify line *)
  elim (dst_inv_abst … H …) -H [3: // |2: skip ] #r #A1 #Hr #HM #HA1 (**) (* simplify line *)
  lapply (pl_sreds_trans … HM1 … (dx:::r) (@B1.𝛌.A1) ?) /2 width=1/ -M #HM1
  lapply (pl_sreds_step_dx … HM1 (◊) ([↙B1]A1) ?) -HM1 // #HM1
  @(dst_step_sn … HM1) /2 width=1/ /4 width=1/
| #p #A #A2 #_ #IHA2 #M1 #H
  elim (dst_inv_abst … H …) -H [3: // |2: skip ] /3 width=5/ (**) (* simplify line *)
| #p #B #B2 #A #_ #IHB2 #M1 #H
  elim (dst_inv_appl … H …) -H [4: // |2,3: skip ] /3 width=7/ (**) (* simplify line *)
| #p #B #A #A2 #_ #IHA2 #M1 #H
  elim (dst_inv_appl … H …) -H [4: // |2,3: skip ] /3 width=7/ (**) (* simplify line *)
]
qed-.

lemma pl_sreds_dst: ∀s,M1,M2. M1 ↦*[s] M2 → M1 ⓢ↦* M2.
#s #M1 #M2 #H @(lstar_ind_r … s M2 H) -s -M2 // /2 width=4 by dst_step_dx/
qed.

lemma dst_inv_pl_sreds_is_standard: ∀M,N. M ⓢ↦* N →
                                    ∃∃r. M ↦*[r] N & is_standard r.
#M #N #H elim H -M -N
[ #s #M #i #Hs #HM
  lapply (is_whd_is_standard … Hs) -Hs /2 width=3/
| #s #M #A1 #A2 #Hs #HM #_ * #r #HA12 #Hr
  lapply (pl_sreds_trans … HM (rc:::r) (𝛌.A2) ?) /2 width=1/ -A1 #HM
  @(ex2_intro … HM) -M -A2 /3 width=1/
| #s #M #B1 #B2 #A1 #A2 #Hs #HM #_ #_ * #rb #HB12 #Hrb * #ra #HA12 #Hra
  lapply (pl_sreds_trans … HM (dx:::ra) (@B1.A2) ?) /2 width=1/ -A1 #HM
  lapply (pl_sreds_trans … HM (sn:::rb) (@B2.A2) ?) /2 width=1/ -B1 #HM
  @(ex2_intro … HM) -M -B2 -A2 >associative_append /3 width=1/
]
qed-.

theorem dst_trans: transitive … dst.
#M1 #M #M2 #HM1 #HM2
elim (dst_inv_pl_sreds_is_standard … HM1) -HM1 #s1 #HM1 #_
elim (dst_inv_pl_sreds_is_standard … HM2) -HM2 #s2 #HM2 #_
lapply (pl_sreds_trans … HM1 … HM2) -M /2 width=2/
qed-.

theorem pl_sreds_standard: ∀s,M,N. M ↦*[s] N → ∃∃r. M ↦*[r] N & is_standard r.
#s #M #N #H
@dst_inv_pl_sreds_is_standard /2 width=2/
qed-.

(* Note: we use "lapply (rewrite_r ?? is_whd … Hq)" (procedural)
         in place of "cut (is_whd (q::r)) [ >Hq ]"  (declarative)
*)
lemma dst_in_whd_swap: ∀p. in_whd p → ∀N1,N2. N1 ↦[p] N2 → ∀M1. M1 ⓢ↦* N1 →
                       ∃∃q,M2. in_whd q & M1 ↦[q] M2 & M2 ⓢ↦* N2.
#p #H @(in_whd_ind … H) -p
[ #N1 #N2 #H1 #M1 #H2
  elim (pl_sred_inv_nil … H1 …) -H1 // #D #C #HN1 #HN2
  elim (dst_inv_appl … H2 … HN1) -N1 #s1 #D1 #N #Hs1 #HM1 #HD1 #H
  elim (dst_inv_abst … H …) -H [3: // |2: skip ] #s2 #C1 #Hs2 #HN #HC1 (**) (* simplify line *)
  lapply (pl_sreds_trans … HM1 … (dx:::s2) (@D1.𝛌.C1) ?) /2 width=1/ -N #HM1
  lapply (pl_sreds_step_dx … HM1 (◊) ([↙D1]C1) ?) -HM1 // #HM1
  elim (pl_sreds_inv_pos … HM1 …) -HM1
  [2: >length_append normalize in ⊢ (??(??%)); // ]
  #q #r #M #Hq #HM1 #HM
  lapply (rewrite_r ?? is_whd … Hq) -Hq /4 width=1/ -s1 -s2 * #Hq #Hr
  @(ex3_2_intro … HM1) -M1 // -q
  @(dst_step_sn … HM) /2 width=1/
| #p #_ #IHp #N1 #N2 #H1 #M1 #H2
  elim (pl_sred_inv_dx … H1 …) -H1 [3: // |2: skip ] #D #C1 #C2 #HC12 #HN1 #HN2 (**) (* simplify line *)
  elim (dst_inv_appl … H2 … HN1) -N1 #s #B #A1 #Hs #HM1 #HBD #HAC1
  elim (IHp … HC12 … HAC1) -p -C1 #p #C1 #Hp #HAC1 #HC12
  lapply (pl_sreds_step_dx … HM1 (dx::p) (@B.C1) ?) -HM1 /2 width=1/ -A1 #HM1
  elim (pl_sreds_inv_pos … HM1 …) -HM1
  [2: >length_append normalize in ⊢ (??(??%)); // ]
  #q #r #M #Hq #HM1 #HM
  lapply (rewrite_r ?? is_whd … Hq) -Hq /4 width=1/ -p -s * #Hq #Hr
  @(ex3_2_intro … HM1) -M1 // -q /2 width=7/
]
qed-.

theorem pl_sreds_in_whd_swap: ∀s,M1,N1. M1 ↦*[s] N1 →
                              ∀p,N2. in_whd p → N1 ↦[p] N2 →
                              ∃∃q,r,M2. in_whd q & M1 ↦[q] M2 & M2 ↦*[r] N2 &
                                        is_standard (q::r).
#s #M1 #N1 #HMN1 #p #N2 #Hp #HN12
lapply (pl_sreds_dst … HMN1) -s #HMN1
elim (dst_in_whd_swap … Hp … HN12 … HMN1) -p -N1 #q #M2 #Hq #HM12 #HMN2
elim (dst_inv_pl_sreds_is_standard … HMN2) -HMN2 /3 width=8/
qed-.
