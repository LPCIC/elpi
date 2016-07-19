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

include "lambda/terms/relocating_substitution.ma".
include "lambda/subterms/relocating_substitution.ma".

(* CARRIER (UNDERLYING TERM) ************************************************)

let rec carrier F on F ≝ match F with
[ SVRef _ i   ⇒ #i
| SAbst _ T   ⇒ 𝛌.(carrier T)
| SAppl _ V T ⇒ @(carrier V).(carrier T)
].

interpretation "carrier (subterms)"
   'ProjectDown F = (carrier F).

notation "hvbox(⇓ term 46 F)"
   non associative with precedence 46
   for @{ 'ProjectDown $F }.

lemma carrier_inv_vref: ∀j,F. ⇓F = #j → ∃b. F = {b}#j.
#j * normalize
[ #b #i #H destruct /2 width=2/
| #b #T #H destruct
| #b #V #T #H destruct
]
qed-.

lemma carrier_inv_abst: ∀C,F. ⇓F = 𝛌.C → ∃∃b,U. ⇓U = C & F = {b}𝛌.U.
#C * normalize
[ #b #i #H destruct
| #b #T #H destruct /2 width=4/
| #b #V #T #H destruct
]
qed-.

lemma carrier_inv_appl: ∀D,C,F. ⇓F = @D.C →
                        ∃∃b,W,U. ⇓W = D & ⇓U = C & F = {b}@W.U.
#D #C * normalize
[ #b #i #H destruct
| #b #T #H destruct
| #b #V #T #H destruct /2 width=6/
]
qed-.

lemma carrier_lift: ∀h,F,d. ⇓ ↑[d, h] F = ↑[d, h] ⇓F.
#h #F elim F -F normalize //
qed.

lemma carrier_dsubst: ∀G,F,d. ⇓ [d ↙ G] F = [d ↙ ⇓G] ⇓F.
#G #F elim F -F [2,3: normalize // ]
#b #i #d elim (lt_or_eq_or_gt i d) #Hid
[ >(sdsubst_vref_lt … Hid) >(dsubst_vref_lt … Hid) //
| destruct normalize //
| >(sdsubst_vref_gt … Hid) >(dsubst_vref_gt … Hid) //
]
qed.
