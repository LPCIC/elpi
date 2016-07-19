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

include "basics/lists/list.ma".

(* MATTER CONCERNING STRONG NORMALIZATION TO BE PUT ELSEWHERE *****************)

(* arithmetics ****************************************************************)

lemma arith1: ∀x,y. (S x) ≰ (S y) → x ≰ y.
#x #y #HS @nmk (elim HS) -HS /3/
qed.

lemma arith2: ∀i,p,k. k ≤ i → i + p - (k + p) = i - k.
#i #p #k #H @plus_to_minus
>commutative_plus >(commutative_plus k) >associative_plus @eq_f /2/
qed.

lemma arith3: ∀x,y,z. x ≰ y → x + z ≰ y + z.
#x #y #z #H @nmk (elim H) -H /3/
qed.

lemma arith4: ∀x,y. S x ≰ y → x≠y → y < x.
#x #y #H1 #H2 lapply (not_le_to_lt … H1) -H1 #H1 @not_eq_to_le_to_lt /2/
qed.

lemma arith5: ∀x,y. x < y → S (y - 1) ≰ x.
#x #y #H @lt_to_not_le <minus_Sn_m /2/
qed.

(* lists **********************************************************************)

lemma length_append: ∀A. ∀(l2,l1:list A). |l1@l2| = |l1| + |l2|.
#A #l2 #l1 elim l1 -l1; normalize //
qed.

(* all(?,P,l) holds when P holds for all members of l *)
let rec all (A:Type[0]) (P:A→Prop) l on l ≝ match l with 
   [ nil        ⇒ True
   | cons hd tl ⇒ P hd ∧ all A P tl
   ].

lemma all_hd: ∀A:Type[0]. ∀P:A→Prop. ∀a. P a → ∀l. all … P l → P (hd … l a).
#A #P #a #Ha #l elim l -l [ #_ @Ha | #b #l #_ #Hl elim Hl -Hl; normalize // ]
qed.

lemma all_tl: ∀A:Type[0]. ∀P:A→Prop. ∀l. all … P l →  all … P (tail … l).
#A #P #l elim l -l // #b #l #IH #Hl elim Hl -Hl; normalize //
qed.

lemma all_nth: ∀A:Type[0]. ∀P:A→Prop. ∀a. P a → ∀i,l. all … P l → P (nth i … l a).
#A #P #a #Ha #i elim i -i [ @all_hd // | #i #IH #l #Hl @IH /2/ ]
qed.

lemma all_append: ∀A,P,l2,l1. all A P l1 → all A P l2 → all A P (l1 @ l2).
#A #P #l2 #l1 elim l1 -l1; normalize // #hd #tl #IH1 #H elim H -H /3/
qed.

(* all2(?,P,l1,l2) holds when P holds for all paired members of l1 and l2 *)
let rec all2 (A,B:Type[0]) (P:A→B→Prop) l1 l2 on l1 ≝ match l1 with
   [ nil          ⇒ l2 = nil ?
   | cons hd1 tl1 ⇒ match l2 with
      [ nil          ⇒ False
      | cons hd2 tl2 ⇒ P hd1 hd2 ∧ all2 A B P tl1 tl2
      ]
   ].

lemma all2_length: ∀A,B:Type[0]. ∀P:A→B→Prop. 
                   ∀l1,l2. all2 … P l1 l2 → |l1|=|l2|.
#A #B #P #l1 elim l1 -l1 [ #l2 #H >H // ]
#x1 #l1 #IH1 #l2 elim l2 -l2 [ #false elim false ]
#x2 #l2 #_ #H elim H -H; normalize /3/
qed. 

lemma all2_hd: ∀A,B:Type[0]. ∀P:A→B→Prop. ∀a,b. P a b →
               ∀l1,l2. all2 … P l1 l2 → P (hd … l1 a) (hd … l2 b).
#A #B #P #a #b #Hab #l1 elim l1 -l1 [ #l2 #H2 >H2 @Hab ]
#x1 #l1 #_ #l2 elim l2 -l2 [ #false elim false ]
#x2 #l2 #_ #H elim H -H; normalize //
qed.

lemma all2_tl: ∀A,B:Type[0]. ∀P:A→B→Prop.
               ∀l1,l2. all2 … P l1 l2 →  all2 … P (tail … l1) (tail … l2).
#A #B #P #l1 elim l1 -l1 [ #l2 #H >H // ]
#x1 #l1 #_ #l2 elim l2 -l2 [ #false elim false ]
#x2 #l2 #_ #H elim H -H; normalize // 
qed.

lemma all2_nth: ∀A,B:Type[0]. ∀P:A→B→Prop. ∀a,b. P a b →
                ∀i,l1,l2. all2 … P l1 l2 → P (nth i … l1 a) (nth i … l2 b).
#A #B #P #a #b #Hab #i elim i -i [ @all2_hd // | #i #IH #l1 #l2 #H @IH /2/ ]
qed.

lemma all2_append: ∀A,B,P,l2,m2. all2 A B P l2 m2 →
                   ∀l1,m1. all2 A B P l1 m1 → all2 A B P (l1 @ l2) (m1 @ m2).
#A #B #P #l2 #m2 #H2 #l1 (elim l1) -l1 [ #m1 #H >H @H2 ] 
#x1 #l1 #IH1 #m2 elim m2 -m2 [ #false elim false ]
#x2 #m2 #_ #H elim H -H /3/
qed.

lemma all2_symmetric: ∀A. ∀P:A→A→Prop. symmetric … P → symmetric … (all2 … P).
#A #P #HP #l1 elim l1 -l1 [ #l2 #H >H // ]
#x1 #l1 #IH1 #l2 elim l2 -l2 [ #false elim false ]
#x2 #l2 #_ #H elim H -H /3/
qed.
