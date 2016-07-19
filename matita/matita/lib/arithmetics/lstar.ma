(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "arithmetics/nat.ma".

(* nat-labeled reflexive and transitive closure *****************************)

definition ltransitive: ∀B:Type[0]. predicate (ℕ→relation B) ≝ λB,R.
                        ∀l1,b1,b. R l1 b1 b → ∀l2,b2. R l2 b b2 → R (l1+l2) b1 b2.

definition inv_ltransitive: ∀B:Type[0]. predicate (ℕ→relation B) ≝
                            λB,R. ∀l1,l2,b1,b2. R (l1+l2) b1 b2 →
                            ∃∃b. R l1 b1 b & R l2 b b2.

inductive lstar (B:Type[0]) (R: relation B): ℕ→relation B ≝
| lstar_O: ∀b. lstar B R 0 b b
| lstar_S: ∀b1,b. R b1 b → ∀l,b2. lstar B R l b b2 → lstar B R (l+1) b1 b2
.

fact lstar_ind_l_aux: ∀B,R,b2. ∀P:relation2 ℕ B.
                      P 0 b2 →
                      (∀l,b1,b. R b1 b → lstar … R l b b2 → P l b → P (l+1) b1) →
                      ∀l,b1,b. lstar … R l b1 b → b = b2 → P l b1.
#B #R #b2 #P #H1 #H2 #l #b1 #b #H elim H -b -b1
[ #b #H destruct /2 width=1/
| #b #b0 #Hb0 #l #b1 #Hb01 #IH #H destruct /3 width=4/
]
qed-.

(* imporeved version of lstar_ind with "left_parameter" *)
lemma lstar_ind_l: ∀B,R,b2. ∀P:relation2 ℕ B.
                   P 0 b2 →
                   (∀l,b1,b. R b1 b → lstar … R l b b2 → P l b → P (l+1) b1) →
                   ∀l,b1. lstar … R l b1 b2 → P l b1.
#B #R #b2 #P #H1 #H2 #l #b1 #Hb12
@(lstar_ind_l_aux … H1 H2 … Hb12) //
qed-.

lemma lstar_step: ∀B,R,b1,b2. R b1 b2 → lstar B R 1 b1 b2.
/2 width=3/
qed.

lemma lstar_dx: ∀B,R,l,b1,b. lstar B R l b1 b → ∀b2. R b b2 →
                lstar B R (l+1) b1 b2.
#B #R #l #b1 #b #H @(lstar_ind_l … l b1 H) -l -b1 /2 width=1/ /3 width=3/
qed.

lemma lstar_inv_O: ∀B,R,l,b1,b2. lstar B R l b1 b2 → 0 = l → b1 = b2.
#B #R #l #b1 #b2 * -l -b1 -b2 //
#b1 #b #_ #l #b2 #_ <plus_n_Sm #H destruct
qed-.

lemma lstar_inv_S: ∀B,R,l,b1,b2. lstar B R l b1 b2 →
                   ∀l0. l0+1 = l →
                   ∃∃b. R b1 b & lstar B R l0 b b2.
#B #R #l #b1 #b2 * -l -b1 -b2
[ #b #l0 <plus_n_Sm #H destruct
| #b1 #b #Hb1 #l #b2 #Hb2 #l0 #H
  lapply (injective_plus_l … H) -H #H destruct /2 width=3/
]
qed-.

lemma lstar_inv_step: ∀B,R,b1,b2. lstar B R 1 b1 b2 → R b1 b2.
#B #R #b1 #b2 #H
elim (lstar_inv_S … 1 … H 0) -H // #b #Hb1 #H
<(lstar_inv_O … R … H ?) -H //
qed-.

theorem lstar_singlevalued: ∀B,R. singlevalued … R →
                            ∀l. singlevalued … (lstar B R l).
#B #R #HR #l #c #c1 #H @(lstar_ind_l … l c H) -l -c
[ /2 width=5 by lstar_inv_O/
| #l #b #b1 #Hb1 #_ #IHbc1 #c2 #H
  elim (lstar_inv_S … R … H l) -H // #b2 #Hb2 #Hbc2
  lapply (HR … Hb1 … Hb2) -b #H destruct /2 width=1/
]
qed-.

theorem lstar_ltransitive: ∀B,R. ltransitive … (lstar B R).
#B #R #l1 #b1 #b #H @(lstar_ind_l … l1 b1 H) -l1 -b1 // /3 width=3/
qed-.

lemma lstar_inv_ltransitive: ∀B,R. inv_ltransitive … (lstar B R).
#B #R #l1 @(nat_ind_plus … l1) -l1 /2 width=3/
#l1 #IHl1 #l2 #b1 #b2 <plus_plus_comm_23 #H
elim (lstar_inv_S … b2 H (l1+l2)) -H // #b #Hb1 #Hb2
elim (IHl1 … Hb2) -IHl1 -Hb2 /3 width=3/
qed-.

lemma lstar_inv_S_dx: ∀B,R,l,b1,b2. lstar B R (l+1) b1 b2 →
                      ∃∃b. lstar B R l b1 b & R b b2.
#B #R #l #b1 #b2 #H
elim (lstar_inv_ltransitive B R … H) -H #b #Hb1 #H
lapply (lstar_inv_step B R … H) -H /2 width=3/
qed-.

inductive lstar_r (B:Type[0]) (R: relation B): ℕ → relation B ≝
| lstar_r_O: ∀b. lstar_r B R 0 b b
| lstar_r_S: ∀l,b1,b. lstar_r B R l b1 b → ∀b2. R b b2 →
             lstar_r B R (l+1) b1 b2
.

lemma lstar_r_sn: ∀B,R,l,b,b2. lstar_r B R l b b2 → ∀b1. R b1 b →
                  lstar_r B R (l+1) b1 b2.
#B #R #l #b #b2 #H elim H -l -b2 /2 width=3/
#l #b1 #b #_ #b2 #Hb2 #IHb1 #b0 #Hb01
@(lstar_r_S … (l+1) … Hb2) -b2 /2 width=1/
qed.

lemma lstar_lstar_r: ∀B,R,l,b1,b2. lstar B R l b1 b2 → lstar_r B R l b1 b2.
#B #R #l #b1 #b2 #H @(lstar_ind_l … l b1 H) -l -b1 // /2 width=3/
qed.

lemma lstar_r_inv_lstar: ∀B,R,l,b1,b2. lstar_r B R l b1 b2 → lstar B R l b1 b2.
#B #R #l #b1 #b2 #H elim H -l -b1 -b2 // /2 width=3/
qed-.

fact lstar_ind_r_aux: ∀B,R,b1. ∀P:relation2 ℕ B.
                      P 0 b1 →
                      (∀l,b,b2. lstar … R l b1 b → R b b2 → P l b → P (l+1) b2) →
                      ∀l,b,b2. lstar … R l b b2 → b = b1 → P l b2.
#B #R #b1 #P #H1 #H2 #l #b #b2 #H elim (lstar_lstar_r … l b b2 H) -l -b -b2
[ #b #H destruct //
| #l #b #b0 #Hb0 #b2 #Hb02 #IHb02 #H destruct /3 width=4 by lstar_r_inv_lstar/
]
qed-.

lemma lstar_ind_r: ∀B,R,b1. ∀P:relation2 ℕ B.
                   P 0 b1 →
                   (∀l,b,b2. lstar … R l b1 b → R b b2 → P l b → P (l+1) b2) →
                   ∀l,b2. lstar … R l b1 b2 → P l b2.
#B #R #b1 #P #H1 #H2 #l #b2 #Hb12
@(lstar_ind_r_aux … H1 H2 … Hb12) //
qed-.

lemma lstar_Conf3: ∀A,B,S,R. Conf3 A B S R → ∀l. Conf3 A B S (lstar … R l).
#A #B #S #R #HSR #l #b #a1 #Ha1 #a2 #H @(lstar_ind_r … l a2 H) -l -a2 // /2 width=3/
qed-.
