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

include "lambda/terms/term.ma".

(* RELOCATION ***************************************************************)

(* Policy: level metavariables : d, e
           height metavariables: h, k
*)
(* Note: indexes start at zero *)
let rec lift h d M on M ≝ match M with
[ VRef i   ⇒ #(tri … i d i (i + h) (i + h))
| Abst A   ⇒ 𝛌. (lift h (d+1) A)
| Appl B A ⇒ @(lift h d B). (lift h d A)
].

interpretation "relocation" 'Lift h d M = (lift h d M).

lemma lift_vref_lt: ∀d,h,i. i < d → ↑[d, h] #i = #i.
normalize /3 width=1/
qed.

lemma lift_vref_ge: ∀d,h,i. d ≤ i → ↑[d, h] #i = #(i+h).
#d #h #i #H elim (le_to_or_lt_eq … H) -H
normalize // /3 width=1/
qed.

lemma lift_id: ∀M,d. ↑[d, 0] M = M.
#M elim M -M
[ #i #d elim (lt_or_ge i d) /2 width=1/
| /3 width=1/
| /3 width=1/
]
qed.

lemma lift_inv_vref_lt: ∀j,d. j < d → ∀h,M. ↑[d, h] M = #j → M = #j.
#j #d #Hjd #h * normalize
[ #i elim (lt_or_eq_or_gt i d) #Hid
  [ >(tri_lt ???? … Hid) -Hid -Hjd //
  | #H destruct >tri_eq in Hjd; #H
    elim (plus_lt_false … H)
  | >(tri_gt ???? … Hid)
    lapply (transitive_lt … Hjd Hid) -d #H #H0 destruct
    elim (plus_lt_false … H)
  ]
| #A #H destruct
| #B #A #H destruct
]
qed.

lemma lift_inv_vref_ge: ∀j,d. d ≤ j → ∀h,M. ↑[d, h] M = #j →
                        d + h ≤ j ∧ M = #(j-h).
#j #d #Hdj #h * normalize
[ #i elim (lt_or_eq_or_gt i d) #Hid
  [ >(tri_lt ???? … Hid) #H destruct
    lapply (le_to_lt_to_lt … Hdj Hid) -Hdj -Hid #H
    elim (lt_refl_false … H)
  | #H -Hdj destruct /2 width=1/
  | >(tri_gt ???? … Hid) #H -Hdj destruct /4 width=1/
  ]
| #A #H destruct
| #B #A #H destruct
]
qed-.

lemma lift_inv_vref_be: ∀j,d,h. d ≤ j → j < d + h → ∀M. ↑[d, h] M = #j → ⊥.
#j #d #h #Hdj #Hjdh #M #H elim (lift_inv_vref_ge … H) -H // -Hdj #Hdhj #_ -M
lapply (lt_to_le_to_lt … Hjdh Hdhj) -d -h #H
elim (lt_refl_false … H)
qed-.

lemma lift_inv_vref_ge_plus: ∀j,d,h. d + h ≤ j →
                             ∀M. ↑[d, h] M = #j → M = #(j-h).
#j #d #h #Hdhj #M #H elim (lift_inv_vref_ge … H) -H // -M /2 width=2/
qed.

lemma lift_inv_abst: ∀C,d,h,M. ↑[d, h] M = 𝛌.C →
                     ∃∃A. ↑[d+1, h] A = C & M = 𝛌.A.
#C #d #h * normalize
[ #i #H destruct
| #A #H destruct /2 width=3/
| #B #A #H destruct
]
qed-.

lemma lift_inv_appl: ∀D,C,d,h,M. ↑[d, h] M = @D.C →
                     ∃∃B,A. ↑[d, h] B = D & ↑[d, h] A = C & M = @B.A.
#D #C #d #h * normalize
[ #i #H destruct
| #A #H destruct
| #B #A #H destruct /2 width=5/
]
qed-.

theorem lift_lift_le: ∀h1,h2,M,d1,d2. d2 ≤ d1 →
                      ↑[d2, h2] ↑[d1, h1] M = ↑[d1 + h2, h1] ↑[d2, h2] M.
#h1 #h2 #M elim M -M
[ #i #d1 #d2 #Hd21 elim (lt_or_ge i d2) #Hid2
  [ lapply (lt_to_le_to_lt … Hid2 Hd21) -Hd21 #Hid1
    >(lift_vref_lt … Hid1) >(lift_vref_lt … Hid2)
    >lift_vref_lt // /2 width=1/
  | >(lift_vref_ge … Hid2) elim (lt_or_ge i d1) #Hid1
    [ >(lift_vref_lt … Hid1) >(lift_vref_ge … Hid2)
      >lift_vref_lt // -d2 /2 width=1/
    | >(lift_vref_ge … Hid1) >lift_vref_ge /2 width=1/
      >lift_vref_ge // /2 width=1/
    ]
  ]
| normalize #A #IHA #d1 #d2 #Hd21 >IHA // /2 width=1/
| normalize #B #A #IHB #IHA #d1 #d2 #Hd21 >IHB >IHA //
]
qed.

theorem lift_lift_be: ∀h1,h2,M,d1,d2. d1 ≤ d2 → d2 ≤ d1 + h1 →
                      ↑[d2, h2] ↑[d1, h1] M = ↑[d1, h1 + h2] M.
#h1 #h2 #M elim M -M
[ #i #d1 #d2 #Hd12 #Hd21 elim (lt_or_ge i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 -Hd21 #Hid2
    >(lift_vref_lt … Hid1) >(lift_vref_lt … Hid1) /2 width=1/
  | lapply (transitive_le … (i+h1) Hd21 ?) -Hd21 -Hd12 /2 width=1/ #Hd2
    >(lift_vref_ge … Hid1) >(lift_vref_ge … Hid1) /2 width=1/
  ]
| normalize #A #IHA #d1 #d2 #Hd12 #Hd21 >IHA // /2 width=1/
| normalize #B #A #IHB #IHA #d1 #d2 #Hd12 #Hd21 >IHB >IHA //
]
qed.

theorem lift_lift_ge: ∀h1,h2,M,d1,d2. d1 + h1 ≤ d2 →
                      ↑[d2, h2] ↑[d1, h1] M = ↑[d1, h1] ↑[d2 - h1, h2] M.
#h1 #h2 #M #d1 #d2 #Hd12
>(lift_lift_le h2 h1) /2 width=1/ <plus_minus_m_m // /2 width=2/
qed.

(* Note: this is "∀h,d. injective … (lift h d)" *)
theorem lift_inj: ∀h,M1,M2,d. ↑[d, h] M2 = ↑[d, h] M1 → M2 = M1.
#h #M1 elim M1 -M1
[ #i #M2 #d #H elim (lt_or_ge i d) #Hid
  [ >(lift_vref_lt … Hid) in H; #H
    >(lift_inv_vref_lt … Hid … H) -M2 -d -h //
  | >(lift_vref_ge … Hid) in H; #H
    >(lift_inv_vref_ge_plus … H) -M2 // /2 width=1/
  ]
| normalize #A1 #IHA1 #M2 #d #H
  elim (lift_inv_abst … H) -H #A2 #HA12 #H destruct
  >(IHA1 … HA12) -IHA1 -A2 //
| normalize #B1 #A1 #IHB1 #IHA1 #M2 #d #H
  elim (lift_inv_appl … H) -H #B2 #A2 #HB12 #HA12 #H destruct
  >(IHB1 … HB12) -IHB1 -B2 >(IHA1 … HA12) -IHA1 -A2 //
]
qed-.

theorem lift_inv_lift_le: ∀h1,h2,M1,M2,d1,d2. d2 ≤ d1 →
                          ↑[d2, h2] M2 = ↑[d1 + h2, h1] M1 →
                          ∃∃M. ↑[d1, h1] M = M2 & ↑[d2, h2] M = M1.
#h1 #h2 #M1 elim M1 -M1
[ #i #M2 #d1 #d2 #Hd21 elim (lt_or_ge i (d1+h2)) #Hid1
  [ >(lift_vref_lt … Hid1) elim (lt_or_ge i d2) #Hid2 #H
    [ lapply (lt_to_le_to_lt … Hid2 Hd21) -Hd21 -Hid1 #Hid1
      >(lift_inv_vref_lt … Hid2 … H) -M2 /3 width=3/
    | elim (lift_inv_vref_ge … H) -H -Hd21 // -Hid2 #Hdh2i #H destruct
      elim (le_inv_plus_l … Hdh2i) -Hdh2i #Hd2i #Hh2i
      @(ex2_intro … (#(i-h2))) [ /4 width=1/ ] -Hid1
      >lift_vref_ge // -Hd2i /3 width=1/ (**) (* auto: needs some help here *)
    ]
  | elim (le_inv_plus_l … Hid1) #Hd1i #Hh2i
    lapply (transitive_le (d2+h2) … Hid1) /2 width=1/ -Hd21 #Hdh2i
    elim (le_inv_plus_l … Hdh2i) #Hd2i #_
    >(lift_vref_ge … Hid1) #H -Hid1
    >(lift_inv_vref_ge_plus … H) -H /2 width=3/ -Hdh2i
    @(ex2_intro … (#(i-h2))) (**) (* auto: needs some help here *)
    [ >lift_vref_ge // -Hd1i /3 width=1/
    | >lift_vref_ge // -Hd2i -Hd1i /3 width=1/
    ]
  ]
| normalize #A1 #IHA1 #M2 #d1 #d2 #Hd21 #H
  elim (lift_inv_abst … H) -H >plus_plus_comm_23 #A2 #HA12 #H destruct
  elim (IHA1 … HA12) -IHA1 -HA12 /2 width=1/ -Hd21 #A #HA2 #HA1
  @(ex2_intro … (𝛌.A)) normalize //
| normalize #B1 #A1 #IHB1 #IHA1 #M2 #d1 #d2 #Hd21 #H
  elim (lift_inv_appl … H) -H #B2 #A2 #HB12 #HA12 #H destruct
  elim (IHB1 … HB12) -IHB1 -HB12 // #B #HB2 #HB1
  elim (IHA1 … HA12) -IHA1 -HA12 // -Hd21 #A #HA2 #HA1
  @(ex2_intro … (@B.A)) normalize //
]
qed-.

theorem lift_inv_lift_be: ∀h1,h2,M1,M2,d1,d2. d1 ≤ d2 → d2 ≤ d1 + h1 →
                          ↑[d2, h2] M2 = ↑[d1, h1 + h2] M1 → ↑[d1, h1] M1 = M2.
#h1 #h2 #M1 elim M1 -M1
[ #i #M2 #d1 #d2 #Hd12 #Hd21 elim (lt_or_ge i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 -Hd21 #Hid2
    >(lift_vref_lt … Hid1) #H >(lift_inv_vref_lt … Hid2 … H) -h2 -M2 -d2 /2 width=1/
  | lapply (transitive_le … (i+h1) Hd21 ?) -Hd12 -Hd21 /2 width=1/ #Hd2
    >(lift_vref_ge … Hid1) #H >(lift_inv_vref_ge_plus … H) -M2 /2 width=1/
  ]
| normalize #A1 #IHA1 #M2 #d1 #d2 #Hd12 #Hd21 #H
  elim (lift_inv_abst … H) -H #A #HA12 #H destruct
  >(IHA1 … HA12) -IHA1 -HA12 // /2 width=1/
| normalize #B1 #A1 #IHB1 #IHA1 #M2 #d1 #d2 #Hd12 #Hd21 #H
  elim (lift_inv_appl … H) -H #B #A #HB12 #HA12 #H destruct
  >(IHB1 … HB12) -IHB1 -HB12 // >(IHA1 … HA12) -IHA1 -HA12 //
]
qed-.

theorem lift_inv_lift_ge: ∀h1,h2,M1,M2,d1,d2. d1 + h1 ≤ d2 →
                          ↑[d2, h2] M2 = ↑[d1, h1] M1 →
                          ∃∃M. ↑[d1, h1] M = M2 & ↑[d2 - h1, h2] M = M1.
#h1 #h2 #M1 #M2 #d1 #d2 #Hd12 #H
elim (le_inv_plus_l … Hd12) -Hd12 #Hd12 #Hh1d2
lapply (sym_eq term … H) -H >(plus_minus_m_m … Hh1d2) in ⊢ (???%→?); -Hh1d2 #H
elim (lift_inv_lift_le … Hd12 … H) -H -Hd12 /2 width=3/
qed-.

definition liftable: predicate (relation term) ≝ λR.
                     ∀h,M1,M2. R M1 M2 → ∀d. R (↑[d, h] M1) (↑[d, h] M2).

definition deliftable_sn: predicate (relation term) ≝ λR.
                          ∀h,N1,N2. R N1 N2 → ∀d,M1. ↑[d, h] M1 = N1 →
                          ∃∃M2. R M1 M2 & ↑[d, h] M2 = N2.

lemma star_liftable: ∀R. liftable R → liftable (star … R).
#R #HR #h #M1 #M2 #H elim H -M2 // /3 width=3/
qed.

lemma star_deliftable_sn: ∀R. deliftable_sn R → deliftable_sn (star … R).
#R #HR #h #N1 #N2 #H elim H -N2 /2 width=3/
#N #N2 #_ #HN2 #IHN1 #d #M1 #HMN1
elim (IHN1 … HMN1) -N1 #M #HM1 #HMN
elim (HR … HN2 … HMN) -N /3 width=3/
qed-.

lemma lstar_liftable: ∀S,R. (∀a. liftable (R a)) →
                      ∀l. liftable (lstar S … R l).
#S #R #HR #l #h #M1 #M2 #H
@(lstar_ind_l … l M1 H) -l -M1 // /3 width=3/
qed.

lemma lstar_deliftable_sn: ∀S,R. (∀a. deliftable_sn (R a)) →
                           ∀l. deliftable_sn (lstar S … R l).
#S #R #HR #l #h #N1 #N2 #H
@(lstar_ind_l … l N1 H) -l -N1 /2 width=3/
#a #l #N1 #N #HN1 #_ #IHN2 #d #M1 #HMN1
elim (HR … HN1 … HMN1) -N1 #M #HM1 #HMN
elim (IHN2 … HMN) -N /3 width=3/
qed-.
