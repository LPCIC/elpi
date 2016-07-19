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

include "lambda/subterms/relocation.ma".

(* RELOCATING SUBSTITUTION **************************************************)

(* Policy: depth (level) metavariables: d, e (as for lift) *)
let rec sdsubst G d F on F ≝ match F with
[ SVRef b i   ⇒ tri … i d ({b}#i) (↑[i] G) ({b}#(i-1))
| SAbst b T   ⇒ {b}𝛌. (sdsubst G (d+1) T)
| SAppl b V T ⇒ {b}@ (sdsubst G d V). (sdsubst G d T)
].

interpretation "relocating substitution for subterms"
   'DSubst G d F = (sdsubst G d F).

lemma sdsubst_vref_lt: ∀b,i,d,G. i < d → [d ↙ G] {b}#i = {b}#i.
normalize /2 width=1/
qed.

lemma sdsubst_vref_eq: ∀b,i,G. [i ↙ G] {b}#i = ↑[i]G.
normalize //
qed.

lemma sdsubst_vref_gt: ∀b,i,d,G. d < i → [d ↙ G] {b}#i = {b}#(i-1).
normalize /2 width=1/
qed.

theorem sdsubst_slift_le: ∀h,G,F,d1,d2. d2 ≤ d1 →
                          [d2 ↙ ↑[d1 - d2, h] G] ↑[d1 + 1, h] F = ↑[d1, h] [d2 ↙ G] F.
#h #G #F elim F -F
[ #b #i #d1 #d2 #Hd21 elim (lt_or_eq_or_gt i d2) #Hid2
  [ lapply (lt_to_le_to_lt … Hid2 Hd21) -Hd21 #Hid1
    >(sdsubst_vref_lt … Hid2) >(slift_vref_lt … Hid1) >slift_vref_lt /2 width=1/
  | destruct >sdsubst_vref_eq >slift_vref_lt /2 width=1/
  | >(sdsubst_vref_gt … Hid2) -Hd21 elim (lt_or_ge (i-1) d1) #Hi1d1
    [ >(slift_vref_lt … Hi1d1) >slift_vref_lt /2 width=1/
    | lapply (ltn_to_ltO … Hid2) #Hi
      >(slift_vref_ge … Hi1d1) >slift_vref_ge /2 width=1/ -Hi1d1 >plus_minus // /3 width=1/
    ]
  ]
| normalize #b #T #IHT #d1 #d2 #Hd21
  lapply (IHT (d1+1) (d2+1) ?) -IHT /2 width=1/
| normalize #b #V #T #IHV #IHT #d1 #d2 #Hd21
  >IHV -IHV // >IHT -IHT //
]
qed.

theorem sdsubst_slift_be: ∀h,G,F,d1,d2. d1 ≤ d2 → d2 ≤ d1 + h →
                          [d2 ↙ G] ↑[d1, h + 1] F = ↑[d1, h] F.
#h #G #F elim F -F
[ #b #i #d1 #d2 #Hd12 #Hd21 elim (lt_or_ge i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 -Hd21 #Hid2
    >(slift_vref_lt … Hid1) >(slift_vref_lt … Hid1) /2 width=1/
  | lapply (transitive_le … (i+h) Hd21 ?) -Hd12 -Hd21 /2 width=1/ #Hd2
    >(slift_vref_ge … Hid1) >(slift_vref_ge … Hid1) -Hid1
    >sdsubst_vref_gt // /2 width=1/
  ]
| normalize #b #T #IHT #d1 #d2 #Hd12 #Hd21
  >IHT -IHT // /2 width=1/
| normalize #b #V #T #IHV #IHT #d1 #d2 #Hd12 #Hd21
  >IHV -IHV // >IHT -IHT //
]
qed.

theorem sdsubst_slift_ge: ∀h,G,F,d1,d2. d1 + h ≤ d2 →
                          [d2 ↙ G] ↑[d1, h] F = ↑[d1, h] [d2 - h ↙ G] F.
#h #G #F elim F -F
[ #b #i #d1 #d2 #Hd12 elim (lt_or_eq_or_gt i (d2-h)) #Hid2h
  [ >(sdsubst_vref_lt … Hid2h) elim (lt_or_ge i d1) #Hid1
    [ lapply (lt_to_le_to_lt … (d1+h) Hid1 ?) -Hid2h // #Hid1h
      lapply (lt_to_le_to_lt … Hid1h Hd12) -Hid1h -Hd12 #Hid2
      >(slift_vref_lt … Hid1) -Hid1 /2 width=1/
    | >(slift_vref_ge … Hid1) -Hid1 -Hd12 /3 width=1/
    ]
  | destruct elim (le_inv_plus_l … Hd12) -Hd12 #Hd12 #Hhd2
    >sdsubst_vref_eq >slift_vref_ge // >slift_slift_be // <plus_minus_m_m //
  | elim (le_inv_plus_l … Hd12) -Hd12 #Hd12 #_
    lapply (le_to_lt_to_lt … Hd12 Hid2h) -Hd12 #Hid1
    lapply (ltn_to_ltO … Hid2h) #Hi
    >(sdsubst_vref_gt … Hid2h)
    >slift_vref_ge /2 width=1/ >slift_vref_ge /2 width=1/ -Hid1
    >sdsubst_vref_gt /2 width=1/ -Hid2h >plus_minus //
  ]
| normalize #b #T #IHT #d1 #d2 #Hd12
  elim (le_inv_plus_l … Hd12) #_ #Hhd2
  >IHT -IHT /2 width=1/ <plus_minus //
| normalize #b #V #T #IHV #IHT #d1 #d2 #Hd12
  >IHV -IHV // >IHT -IHT //
]
qed.

theorem sdsubst_sdsubst_ge: ∀G1,G2,F,d1,d2. d1 ≤ d2 →
                            [d2 ↙ G2] [d1 ↙ G1] F = [d1 ↙ [d2 - d1 ↙ G2] G1] [d2 + 1 ↙ G2] F.
#G1 #G2 #F elim F -F
[ #b #i #d1 #d2 #Hd12 elim (lt_or_eq_or_gt i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2
    >(sdsubst_vref_lt … Hid1) >(sdsubst_vref_lt … Hid2) >sdsubst_vref_lt /2 width=1/
  | destruct >sdsubst_vref_eq >sdsubst_vref_lt /2 width=1/
  | >(sdsubst_vref_gt … Hid1) elim (lt_or_eq_or_gt i (d2+1)) #Hid2
    [ lapply (ltn_to_ltO … Hid1) #Hi
      >(sdsubst_vref_lt … Hid2) >sdsubst_vref_lt /2 width=1/
    | destruct /2 width=1/
    | lapply (le_to_lt_to_lt (d1+1) … Hid2) -Hid1 /2 width=1/ -Hd12 #Hid1
      >(sdsubst_vref_gt … Hid2) >sdsubst_vref_gt /2 width=1/
      >sdsubst_vref_gt // /2 width=1/
    ]
  ]
| normalize #b #T #IHT #d1 #d2 #Hd12
  lapply (IHT (d1+1) (d2+1) ?) -IHT /2 width=1/
| normalize #b #V #T #IHV #IHT #d1 #d2 #Hd12
  >IHV -IHV // >IHT -IHT //
]
qed.

theorem sdsubst_sdsubst_lt: ∀G1,G2,F,d1,d2. d2 < d1 →
                            [d2 ↙ [d1 - d2 -1 ↙ G1] G2] [d1 ↙ G1] F = [d1 - 1 ↙ G1] [d2 ↙ G2] F.
#G1 #G2 #F #d1 #d2 #Hd21
lapply (ltn_to_ltO … Hd21) #Hd1
>sdsubst_sdsubst_ge in ⊢ (???%); /2 width=1/ <plus_minus_m_m //
qed.

definition sdsubstable_f_dx: ∀S:Type[0]. (S → ?) → predicate (relation subterms) ≝ λS,f,R.
                             ∀G,F1,F2. R F1 F2 → ∀d. R ([d ↙ (f G)] F1) ([d ↙ (f G)] F2).

lemma lstar_sdsubstable_f_dx: ∀S1,f,S2,R. (∀a. sdsubstable_f_dx S1 f (R a)) →
                              ∀l. sdsubstable_f_dx S1 f (lstar S2 … R l).
#S1 #f #S2 #R #HR #l #G #F1 #F2 #H
@(lstar_ind_l … l F1 H) -l -F1 // /3 width=3/
qed.
(*
definition sdsubstable_dx: predicate (relation subterms) ≝ λR.
                           ∀G,F1,F2. R F1 F2 → ∀d. R ([d ↙ G] F1) ([d ↙ G] F2).

definition sdsubstable: predicate (relation subterms) ≝ λR.
                        ∀G1,G2. R G1 G2 → ∀F1,F2. R F1 F2 → ∀d. R ([d ↙ G1] F1) ([d ↙ G2] F2).

lemma star_sdsubstable_dx: ∀R. sdsubstable_dx R → sdsubstable_dx (star … R).
#R #HR #G #F1 #F2 #H elim H -F2 // /3 width=3/
qed.

lemma lstar_sdsubstable_dx: ∀S,R. (∀a. sdsubstable_dx (R a)) →
                            ∀l. sdsubstable_dx (lstar S … R l).
#S #R #HR #l #G #F1 #F2 #H
@(lstar_ind_l … l F1 H) -l -F1 // /3 width=3/
qed.

lemma star_sdsubstable: ∀R. reflexive ? R →
                        sdsubstable R → sdsubstable (star … R).
#R #H1R #H2 #G1 #G2 #H elim H -G2 /3 width=1/ /3 width=5/
qed.
*)
