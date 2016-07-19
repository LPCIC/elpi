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

include "lambda/subterms/subterms.ma".

(* RELOCATION FOR SUBTERMS **************************************************)

let rec slift h d E on E ≝ match E with
[ SVRef b i   ⇒ {b}#(tri … i d i (i + h) (i + h))
| SAbst b T   ⇒ {b}𝛌.(slift h (d+1) T)
| SAppl b V T ⇒ {b}@(slift h d V).(slift h d T)
].

interpretation "relocation for subterms" 'Lift h d E = (slift h d E).

lemma slift_vref_lt: ∀b,d,h,i. i < d → ↑[d, h] {b}#i = {b}#i.
normalize /3 width=1/
qed.

lemma slift_vref_ge: ∀b,d,h,i. d ≤ i → ↑[d, h] {b}#i = {b}#(i+h).
#b #d #h #i #H elim (le_to_or_lt_eq … H) -H
normalize // /3 width=1/
qed.

lemma slift_id: ∀E,d. ↑[d, 0] E = E.
#E elim E -E
[ #b #i #d elim (lt_or_ge i d) /2 width=1/
| /3 width=1/
| /3 width=1/
]
qed.

lemma slift_inv_vref_lt: ∀c,j,d. j < d → ∀h,E. ↑[d, h] E = {c}#j → E = {c}#j.
#c #j #d #Hjd #h * normalize
[ #b #i elim (lt_or_eq_or_gt i d) #Hid
  [ >(tri_lt ???? … Hid) -Hid -Hjd //
  | #H destruct >tri_eq in Hjd; #H
    elim (plus_lt_false … H)
  | >(tri_gt ???? … Hid)
    lapply (transitive_lt … Hjd Hid) -d #H #H0 destruct
    elim (plus_lt_false … H)
  ]
| #b #T #H destruct
| #b #V #T #H destruct
]
qed.

lemma slift_inv_vref_ge: ∀c,j,d. d ≤ j → ∀h,E. ↑[d, h] E = {c}#j →
                         d + h ≤ j ∧ E = {c}#(j-h).
#c #j #d #Hdj #h * normalize
[ #b #i elim (lt_or_eq_or_gt i d) #Hid
  [ >(tri_lt ???? … Hid) #H destruct
    lapply (le_to_lt_to_lt … Hdj Hid) -Hdj -Hid #H
    elim (lt_refl_false … H)
  | #H -Hdj destruct /2 width=1/
  | >(tri_gt ???? … Hid) #H -Hdj destruct /4 width=1/
  ]
| #b #T #H destruct
| #b #V #T #H destruct
]
qed-.

lemma slift_inv_vref_be: ∀c,j,d,h. d ≤ j → j < d + h → ∀E. ↑[d, h] E = {c}#j → ⊥.
#c #j #d #h #Hdj #Hjdh #E #H elim (slift_inv_vref_ge … H) -H // -Hdj #Hdhj #_ -E
lapply (lt_to_le_to_lt … Hjdh Hdhj) -d -h #H
elim (lt_refl_false … H)
qed-.

lemma slift_inv_vref_ge_plus: ∀c,j,d,h. d + h ≤ j →
                              ∀E. ↑[d, h] E = {c}#j → E = {c}#(j-h).
#c #j #d #h #Hdhj #E #H elim (slift_inv_vref_ge … H) -H // -E /2 width=2/
qed.

lemma slift_inv_abst: ∀c,U,d,h,E. ↑[d, h] E = {c}𝛌.U →
                      ∃∃T. ↑[d+1, h] T = U & E = {c}𝛌.T.
#c #U #d #h * normalize
[ #b #i #H destruct
| #b #T #H destruct /2 width=3/
| #b #V #T #H destruct
]
qed-.

lemma slift_inv_appl: ∀c,W,U,d,h,E. ↑[d, h] E = {c}@W.U →
                      ∃∃V,T. ↑[d, h] V = W & ↑[d, h] T = U & E = {c}@V.T.
#c #W #U #d #h * normalize
[ #b #i #H destruct
| #b #T #H destruct
| #b #V #T #H destruct /2 width=5/
]
qed-.

theorem slift_slift_le: ∀h1,h2,E,d1,d2. d2 ≤ d1 →
                        ↑[d2, h2] ↑[d1, h1] E = ↑[d1 + h2, h1] ↑[d2, h2] E.
#h1 #h2 #E elim E -E
[ #b #i #d1 #d2 #Hd21 elim (lt_or_ge i d2) #Hid2
  [ lapply (lt_to_le_to_lt … Hid2 Hd21) -Hd21 #Hid1
    >(slift_vref_lt … Hid1) >(slift_vref_lt … Hid2)
    >slift_vref_lt // /2 width=1/
  | >(slift_vref_ge … Hid2) elim (lt_or_ge i d1) #Hid1
    [ >(slift_vref_lt … Hid1) >(slift_vref_ge … Hid2)
      >slift_vref_lt // -d2 /2 width=1/
    | >(slift_vref_ge … Hid1) >slift_vref_ge /2 width=1/
      >slift_vref_ge // /2 width=1/
    ]
  ]
| normalize #b #T #IHT #d1 #d2 #Hd21 >IHT // /2 width=1/
| normalize #b #V #T #IHV #IHT #d1 #d2 #Hd21 >IHV >IHT //
]
qed.

theorem slift_slift_be: ∀h1,h2,E,d1,d2. d1 ≤ d2 → d2 ≤ d1 + h1 →
                        ↑[d2, h2] ↑[d1, h1] E = ↑[d1, h1 + h2] E.
#h1 #h2 #E elim E -E
[ #b #i #d1 #d2 #Hd12 #Hd21 elim (lt_or_ge i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 -Hd21 #Hid2
    >(slift_vref_lt … Hid1) >(slift_vref_lt … Hid1) /2 width=1/
  | lapply (transitive_le … (i+h1) Hd21 ?) -Hd21 -Hd12 /2 width=1/ #Hd2
    >(slift_vref_ge … Hid1) >(slift_vref_ge … Hid1) /2 width=1/
  ]
| normalize #b #T #IHT #d1 #d2 #Hd12 #Hd21 >IHT // /2 width=1/
| normalize #b #V #T #IHV #IHT #d1 #d2 #Hd12 #Hd21 >IHV >IHT //
]
qed.

theorem slift_slift_ge: ∀h1,h2,E,d1,d2. d1 + h1 ≤ d2 →
                        ↑[d2, h2] ↑[d1, h1] E = ↑[d1, h1] ↑[d2 - h1, h2] E.
#h1 #h2 #E #d1 #d2 #Hd12
>(slift_slift_le h2 h1) /2 width=1/ <plus_minus_m_m // /2 width=2/
qed.

(* Note: this is "∀h,d. injective … (slift h d)" *)
theorem slift_inj: ∀h,E1,E2,d. ↑[d, h] E2 = ↑[d, h] E1 → E2 = E1.
#h #E1 elim E1 -E1
[ #b #i #E2 #d #H elim (lt_or_ge i d) #Hid
  [ >(slift_vref_lt … Hid) in H; #H
    >(slift_inv_vref_lt … Hid … H) -E2 -d -h //
  | >(slift_vref_ge … Hid) in H; #H
    >(slift_inv_vref_ge_plus … H) -E2 // /2 width=1/
  ]
| normalize #b #T1 #IHT1 #E2 #d #H
  elim (slift_inv_abst … H) -H #T2 #HT12 #H destruct
  >(IHT1 … HT12) -IHT1 -T2 //
| normalize #b #V1 #T1 #IHV1 #IHT1 #E2 #d #H
  elim (slift_inv_appl … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  >(IHV1 … HV12) -IHV1 -V2 >(IHT1 … HT12) -IHT1 -T2 //
]
qed-.

theorem slift_inv_slift_le: ∀h1,h2,E1,E2,d1,d2. d2 ≤ d1 →
                            ↑[d2, h2] E2 = ↑[d1 + h2, h1] E1 →
                            ∃∃E. ↑[d1, h1] E = E2 & ↑[d2, h2] E = E1.
#h1 #h2 #E1 elim E1 -E1
[ #b #i #E2 #d1 #d2 #Hd21 elim (lt_or_ge i (d1+h2)) #Hid1
  [ >(slift_vref_lt … Hid1) elim (lt_or_ge i d2) #Hid2 #H
    [ lapply (lt_to_le_to_lt … Hid2 Hd21) -Hd21 -Hid1 #Hid1
      >(slift_inv_vref_lt … Hid2 … H) -E2 /3 width=3/
    | elim (slift_inv_vref_ge … H) -H -Hd21 // -Hid2 #Hdh2i #H destruct
      elim (le_inv_plus_l … Hdh2i) -Hdh2i #Hd2i #Hh2i
      @(ex2_intro … ({b}#(i-h2))) [ /4 width=1/ ] -Hid1
      >slift_vref_ge // -Hd2i /3 width=1/ (**) (* auto: needs some help here *)
    ]
  | elim (le_inv_plus_l … Hid1) #Hd1i #Hh2i
    lapply (transitive_le (d2+h2) … Hid1) /2 width=1/ -Hd21 #Hdh2i
    elim (le_inv_plus_l … Hdh2i) #Hd2i #_
    >(slift_vref_ge … Hid1) #H -Hid1
    >(slift_inv_vref_ge_plus … H) -H /2 width=3/ -Hdh2i
    @(ex2_intro … ({b}#(i-h2))) (**) (* auto: needs some help here *)
    [ >slift_vref_ge // -Hd1i /3 width=1/
    | >slift_vref_ge // -Hd2i -Hd1i /3 width=1/
    ]
  ]
| normalize #b #T1 #IHT1 #E2 #d1 #d2 #Hd21 #H
  elim (slift_inv_abst … H) -H >plus_plus_comm_23 #T2 #HT12 #H destruct
  elim (IHT1 … HT12) -IHT1 -HT12 /2 width=1/ -Hd21 #T #HT2 #HT1
  @(ex2_intro … ({b}𝛌.T)) normalize //
| normalize #b #V1 #T1 #IHV1 #IHT1 #E2 #d1 #d2 #Hd21 #H
  elim (slift_inv_appl … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  elim (IHV1 … HV12) -IHV1 -HV12 // #V #HV2 #HV1
  elim (IHT1 … HT12) -IHT1 -HT12 // -Hd21 #T #HT2 #HT1
  @(ex2_intro … ({b}@V.T)) normalize //
]
qed-.

theorem slift_inv_slift_be: ∀h1,h2,E1,E2,d1,d2. d1 ≤ d2 → d2 ≤ d1 + h1 →
                            ↑[d2, h2] E2 = ↑[d1, h1 + h2] E1 → ↑[d1, h1] E1 = E2.
#h1 #h2 #E1 elim E1 -E1
[ #b #i #E2 #d1 #d2 #Hd12 #Hd21 elim (lt_or_ge i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 -Hd21 #Hid2
    >(slift_vref_lt … Hid1) #H >(slift_inv_vref_lt … Hid2 … H) -h2 -E2 -d2 /2 width=1/
  | lapply (transitive_le … (i+h1) Hd21 ?) -Hd12 -Hd21 /2 width=1/ #Hd2
    >(slift_vref_ge … Hid1) #H >(slift_inv_vref_ge_plus … H) -E2 /2 width=1/
  ]
| normalize #b #T1 #IHT1 #E2 #d1 #d2 #Hd12 #Hd21 #H
  elim (slift_inv_abst … H) -H #T #HT12 #H destruct
  >(IHT1 … HT12) -IHT1 -HT12 // /2 width=1/
| normalize #b #V1 #T1 #IHV1 #IHT1 #E2 #d1 #d2 #Hd12 #Hd21 #H
  elim (slift_inv_appl … H) -H #V #T #HV12 #HT12 #H destruct
  >(IHV1 … HV12) -IHV1 -HV12 // >(IHT1 … HT12) -IHT1 -HT12 //
]
qed-.

theorem slift_inv_slift_ge: ∀h1,h2,E1,E2,d1,d2. d1 + h1 ≤ d2 →
                            ↑[d2, h2] E2 = ↑[d1, h1] E1 →
                            ∃∃E. ↑[d1, h1] E = E2 & ↑[d2 - h1, h2] E = E1.
#h1 #h2 #E1 #E2 #d1 #d2 #Hd12 #H
elim (le_inv_plus_l … Hd12) -Hd12 #Hd12 #Hh1d2
lapply (sym_eq subterms … H) -H >(plus_minus_m_m … Hh1d2) in ⊢ (???%→?); -Hh1d2 #H
elim (slift_inv_slift_le … Hd12 … H) -H -Hd12 /2 width=3/
qed-.

definition sliftable: predicate (relation subterms) ≝ λR.
                      ∀h,F1,F2. R F1 F2 → ∀d. R (↑[d, h] F1) (↑[d, h] F2).

definition sdeliftable_sn: predicate (relation subterms) ≝ λR.
                           ∀h,G1,G2. R G1 G2 → ∀d,F1. ↑[d, h] F1 = G1 →
                           ∃∃F2. R F1 F2 & ↑[d, h] F2 = G2.
(*
lemma star_sliftable: ∀R. sliftable R → sliftable (star … R).
#R #HR #h #F1 #F2 #H elim H -F2 // /3 width=3/
qed.

lemma star_deliftable_sn: ∀R. sdeliftable_sn R → sdeliftable_sn (star … R).
#R #HR #h #G1 #G2 #H elim H -G2 /2 width=3/
#G #G2 #_ #HG2 #IHG1 #d #F1 #HFG1
elim (IHG1 … HFG1) -G1 #F #HF1 #HFG
elim (HR … HG2 … HFG) -G /3 width=3/
qed-.
*)
lemma lstar_sliftable: ∀S,R. (∀a. sliftable (R a)) →
                       ∀l. sliftable (lstar S … R l).
#S #R #HR #l #h #F1 #F2 #H
@(lstar_ind_l … l F1 H) -l -F1 // /3 width=3/
qed.

lemma lstar_sdeliftable_sn: ∀S,R. (∀a. sdeliftable_sn (R a)) →
                            ∀l. sdeliftable_sn (lstar S … R l).
#S #R #HR #l #h #G1 #G2 #H
@(lstar_ind_l … l G1 H) -l -G1 /2 width=3/
#a #l #G1 #G #HG1 #_ #IHG2 #d #F1 #HFG1
elim (HR … HG1 … HFG1) -G1 #F #HF1 #HFG
elim (IHG2 … HFG) -G /3 width=3/
qed-.
