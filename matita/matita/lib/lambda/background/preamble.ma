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

include "basics/star1.ma".
include "basics/lists/lstar.ma".
include "arithmetics/exp.ma".

include "lambda/background/xoa_notation.ma".
include "lambda/background/xoa.ma".
include "lambda/background/notation.ma".

(* logic *)

(* Note: For some reason this cannot be in the standard library *) 
interpretation "logical false" 'false = False.

(* booleans *)

(* Note: For some reason this cannot be in the standard library *) 
interpretation "boolean false" 'false = false.

(* Note: For some reason this cannot be in the standard library *) 
interpretation "boolean true" 'true = true.

(* arithmetics *)

lemma lt_refl_false: ∀n. n < n → ⊥.
#n #H elim (lt_to_not_eq … H) -H /2 width=1/
qed-.

lemma lt_zero_false: ∀n. n < 0 → ⊥.
#n #H elim (lt_to_not_le … H) -H /2 width=1/
qed-.

lemma plus_lt_false: ∀m,n. m + n < m → ⊥.
#m #n #H elim (lt_to_not_le … H) -H /2 width=1/
qed-.

lemma lt_or_eq_or_gt: ∀m,n. ∨∨ m < n | n = m | n < m.
#m #n elim (lt_or_ge m n) /2 width=1/
#H elim H -m /2 width=1/
#m #Hm * #H /2 width=1/ /3 width=1/
qed-.

(* trichotomy operator *)

(* Note: this is "if eqb n1 n2 then a2 else if leb n1 n2 then a1 else a3" *)
let rec tri (A:Type[0]) n1 n2 a1 a2 a3 on n1 : A ≝
  match n1 with 
  [ O    ⇒ match n2 with [ O ⇒ a2 | S n2 ⇒ a1 ]
  | S n1 ⇒ match n2 with [ O ⇒ a3 | S n2 ⇒ tri A n1 n2 a1 a2 a3 ]
  ].

lemma tri_lt: ∀A,a1,a2,a3,n2,n1. n1 < n2 → tri A n1 n2 a1 a2 a3 = a1.
#A #a1 #a2 #a3 #n2 elim n2 -n2
[ #n1 #H elim (lt_zero_false … H)
| #n2 #IH #n1 elim n1 -n1 // /3 width=1/
]
qed.

lemma tri_eq: ∀A,a1,a2,a3,n. tri A n n a1 a2 a3 = a2.
#A #a1 #a2 #a3 #n elim n -n normalize //
qed.

lemma tri_gt: ∀A,a1,a2,a3,n1,n2. n2 < n1 → tri A n1 n2 a1 a2 a3 = a3.
#A #a1 #a2 #a3 #n1 elim n1 -n1
[ #n2 #H elim (lt_zero_false … H)
| #n1 #IH #n2 elim n2 -n2 // /3 width=1/
]
qed.

(* lists *)

(* Note: notation for nil not involving brackets *)
notation > "◊"
  non associative with precedence 90
  for @{'nil}.

lemma list_inv: ∀A. ∀l:list A. ◊ = l ∨ ∃∃a0,l0. a0 :: l0 = l.
#A * /2 width=1/ /3 width=3/
qed-.

definition map_cons: ∀A. A → list (list A) → list (list A) ≝ λA,a.
                     map … (cons … a).

interpretation "map_cons" 'ho_cons a l = (map_cons ? a l).

notation "hvbox(a ::: break l)"
  right associative with precedence 47
  for @{'ho_cons $a $l}.

lemma map_cons_inv_nil: ∀A,a,l1. map_cons A a l1 = ◊ → ◊ = l1.
#A #a * // normalize #a1 #l1 #H destruct
qed-.

lemma map_cons_inv_cons: ∀A,a,a2,l2,l1. map_cons A a l1 = a2::l2 →
                         ∃∃a1,l. a::a1 = a2 & a:::l = l2 & a1::l = l1.
#A #a #a2 #l2 * normalize
[ #H destruct
| #a1 #l1 #H destruct /2 width=5/
]
qed-.

lemma map_cons_append: ∀A,a,l1,l2. map_cons A a (l1@l2) =
                       map_cons A a l1 @ map_cons A a l2.
#A #a #l1 elim l1 -l1 // normalize /2 width=1/
qed.

(* lstar *)

(* Note: this cannot be in lib because of the missing xoa quantifier *)
lemma lstar_inv_pos: ∀A,B,R,l,b1,b2. lstar A B R l b1 b2 → 0 < |l| →
                     ∃∃a,ll,b. a::ll = l & R a b1 b & lstar A B R ll b b2.
#A #B #R #l #b1 #b2 #H @(lstar_ind_l … l b1 H) -l -b1
[ #H elim (lt_refl_false … H)
| #a #ll #b1 #b #Hb1 #Hb2 #_ #_ /2 width=6/ (**) (* auto fail if we do not remove the inductive premise *)
]
qed-.
