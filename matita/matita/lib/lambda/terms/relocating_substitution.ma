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

include "lambda/terms/relocation.ma".

(* RELOCATING SUBSTITUTION **************************************************)

(* Policy: depth (level) metavariables: d, e (as for lift) *)
let rec dsubst N d M on M ≝ match M with
[ VRef i   ⇒ tri … i d (#i) (↑[i] N) (#(i-1))
| Abst A   ⇒ 𝛌. (dsubst N (d+1) A)
| Appl B A ⇒ @ (dsubst N d B). (dsubst N d A)
].

interpretation "relocating substitution"
   'DSubst N d M = (dsubst N d M).

lemma dsubst_vref_lt: ∀i,d,N. i < d → [d ↙ N] #i = #i.
normalize /2 width=1/
qed.

lemma dsubst_vref_eq: ∀i,N. [i ↙ N] #i = ↑[i]N.
normalize //
qed.

lemma dsubst_vref_gt: ∀i,d,N. d < i → [d ↙ N] #i = #(i-1).
normalize /2 width=1/
qed.

theorem dsubst_lift_le: ∀h,N,M,d1,d2. d2 ≤ d1 →
                        [d2 ↙ ↑[d1 - d2, h] N] ↑[d1 + 1, h] M = ↑[d1, h] [d2 ↙ N] M.
#h #N #M elim M -M
[ #i #d1 #d2 #Hd21 elim (lt_or_eq_or_gt i d2) #Hid2
  [ lapply (lt_to_le_to_lt … Hid2 Hd21) -Hd21 #Hid1
    >(dsubst_vref_lt … Hid2) >(lift_vref_lt … Hid1) >lift_vref_lt /2 width=1/
  | destruct >dsubst_vref_eq >lift_vref_lt /2 width=1/
  | >(dsubst_vref_gt … Hid2) -Hd21 elim (lt_or_ge (i-1) d1) #Hi1d1
    [ >(lift_vref_lt … Hi1d1) >lift_vref_lt /2 width=1/
    | lapply (ltn_to_ltO … Hid2) #Hi
      >(lift_vref_ge … Hi1d1) >lift_vref_ge /2 width=1/ -Hi1d1 >plus_minus // /3 width=1/
    ]
  ]
| normalize #A #IHA #d1 #d2 #Hd21
  lapply (IHA (d1+1) (d2+1) ?) -IHA /2 width=1/
| normalize #B #A #IHB #IHA #d1 #d2 #Hd21
  >IHB -IHB // >IHA -IHA //
]
qed.

theorem dsubst_lift_be: ∀h,N,M,d1,d2. d1 ≤ d2 → d2 ≤ d1 + h →
                        [d2 ↙ N] ↑[d1, h + 1] M = ↑[d1, h] M.
#h #N #M elim M -M
[ #i #d1 #d2 #Hd12 #Hd21 elim (lt_or_ge i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 -Hd21 #Hid2
    >(lift_vref_lt … Hid1) >(lift_vref_lt … Hid1) /2 width=1/
  | lapply (transitive_le … (i+h) Hd21 ?) -Hd12 -Hd21 /2 width=1/ #Hd2
    >(lift_vref_ge … Hid1) >(lift_vref_ge … Hid1) -Hid1
    >dsubst_vref_gt // /2 width=1/
  ]
| normalize #A #IHA #d1 #d2 #Hd12 #Hd21
  >IHA -IHA // /2 width=1/
| normalize #B #A #IHB #IHA #d1 #d2 #Hd12 #Hd21
  >IHB -IHB // >IHA -IHA //
]
qed.

theorem dsubst_lift_ge: ∀h,N,M,d1,d2. d1 + h ≤ d2 →
                        [d2 ↙ N] ↑[d1, h] M = ↑[d1, h] [d2 - h ↙ N] M.
#h #N #M elim M -M
[ #i #d1 #d2 #Hd12 elim (lt_or_eq_or_gt i (d2-h)) #Hid2h
  [ >(dsubst_vref_lt … Hid2h) elim (lt_or_ge i d1) #Hid1
    [ lapply (lt_to_le_to_lt … (d1+h) Hid1 ?) -Hid2h // #Hid1h
      lapply (lt_to_le_to_lt … Hid1h Hd12) -Hid1h -Hd12 #Hid2
      >(lift_vref_lt … Hid1) -Hid1 /2 width=1/
    | >(lift_vref_ge … Hid1) -Hid1 -Hd12 /3 width=1/
    ]
  | destruct elim (le_inv_plus_l … Hd12) -Hd12 #Hd12 #Hhd2
    >dsubst_vref_eq >lift_vref_ge // >lift_lift_be // <plus_minus_m_m //
  | elim (le_inv_plus_l … Hd12) -Hd12 #Hd12 #_
    lapply (le_to_lt_to_lt … Hd12 Hid2h) -Hd12 #Hid1
    lapply (ltn_to_ltO … Hid2h) #Hi
    >(dsubst_vref_gt … Hid2h)
    >lift_vref_ge /2 width=1/ >lift_vref_ge /2 width=1/ -Hid1
    >dsubst_vref_gt /2 width=1/ -Hid2h >plus_minus //
  ]
| normalize #A #IHA #d1 #d2 #Hd12
  elim (le_inv_plus_l … Hd12) #_ #Hhd2
  >IHA -IHA /2 width=1/ <plus_minus //
| normalize #B #A #IHB #IHA #d1 #d2 #Hd12
  >IHB -IHB // >IHA -IHA //
]
qed.

theorem dsubst_dsubst_ge: ∀N1,N2,M,d1,d2. d1 ≤ d2 →
                          [d2 ↙ N2] [d1 ↙ N1] M = [d1 ↙ [d2 - d1 ↙ N2] N1] [d2 + 1 ↙ N2] M.
#N1 #N2 #M elim M -M
[ #i #d1 #d2 #Hd12 elim (lt_or_eq_or_gt i d1) #Hid1
  [ lapply (lt_to_le_to_lt … Hid1 Hd12) -Hd12 #Hid2
    >(dsubst_vref_lt … Hid1) >(dsubst_vref_lt … Hid2) >dsubst_vref_lt /2 width=1/
  | destruct >dsubst_vref_eq >dsubst_vref_lt /2 width=1/
  | >(dsubst_vref_gt … Hid1) elim (lt_or_eq_or_gt i (d2+1)) #Hid2
    [ lapply (ltn_to_ltO … Hid1) #Hi
      >(dsubst_vref_lt … Hid2) >dsubst_vref_lt /2 width=1/
    | destruct /2 width=1/
    | lapply (le_to_lt_to_lt (d1+1) … Hid2) -Hid1 /2 width=1/ -Hd12 #Hid1
      >(dsubst_vref_gt … Hid2) >dsubst_vref_gt /2 width=1/
      >dsubst_vref_gt // /2 width=1/
    ]
  ]
| normalize #A #IHA #d1 #d2 #Hd12
  lapply (IHA (d1+1) (d2+1) ?) -IHA /2 width=1/
| normalize #B #A #IHB #IHA #d1 #d2 #Hd12
  >IHB -IHB // >IHA -IHA //
]
qed.

theorem dsubst_dsubst_lt: ∀N1,N2,M,d1,d2. d2 < d1 →
                          [d2 ↙ [d1 - d2 -1 ↙ N1] N2] [d1 ↙ N1] M = [d1 - 1 ↙ N1] [d2 ↙ N2] M.
#N1 #N2 #M #d1 #d2 #Hd21
lapply (ltn_to_ltO … Hd21) #Hd1
>dsubst_dsubst_ge in ⊢ (???%); /2 width=1/ <plus_minus_m_m //
qed.

definition dsubstable_dx: predicate (relation term) ≝ λR.
                          ∀N,M1,M2. R M1 M2 → ∀d. R ([d ↙ N] M1) ([d ↙ N] M2).

definition dsubstable: predicate (relation term) ≝ λR.
                       ∀N1,N2. R N1 N2 → ∀M1,M2. R M1 M2 → ∀d. R ([d ↙ N1] M1) ([d ↙ N2] M2).

lemma star_dsubstable_dx: ∀R. dsubstable_dx R → dsubstable_dx (star … R).
#R #HR #N #M1 #M2 #H elim H -M2 // /3 width=3/
qed.

lemma lstar_dsubstable_dx: ∀S,R. (∀a. dsubstable_dx (R a)) →
                           ∀l. dsubstable_dx (lstar S … R l).
#S #R #HR #l #N #M1 #M2 #H
@(lstar_ind_l … l M1 H) -l -M1 // /3 width=3/
qed.

lemma star_dsubstable: ∀R. reflexive ? R →
                       dsubstable R → dsubstable (star … R).
#R #H1R #H2 #N1 #N2 #H elim H -N2 /3 width=1/ /3 width=5/
qed.
