(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)

include "basics/vectors.ma".
include "basics/finset.ma".

(* DeqSet *)
let rec eq_Vector (A:DeqSet) n on n ≝ 
  match n return (λn.∀v1,v2:Vector A n.bool) with 
  [O ⇒ λv1,v2.true
  |S m ⇒ λv1,v2. vec_hd A m v1 == vec_hd A m v2 ∧ 
         eq_Vector A m (vec_tail A (S m) v1) (vec_tail A (S m) v2)].
      
lemma eq_Vector_S : ∀A:DeqSet.∀n,v1,v2. 
  eq_Vector A (S n) v1 v2 = 
    (vec_hd A n v1 == vec_hd A n v2 ∧ 
     eq_Vector A n (vec_tail A (S n) v1) (vec_tail A (S n) v2)).
// qed.
         
axiom eq_Vector_S1 : ∀A:DeqSet.∀n,a1,a2,v1,v2. 
  eq_Vector A (S n) (vec_cons A a1 n v1) (vec_cons A a2 n v2) =
  (a1 == a2 ∧ eq_Vector A n v1 v2).
 
(* uses proof irrelevance *)
axiom eq_Vector_true: ∀A:DeqSet.∀n,v1,v2.
  eq_Vector A n v1 v2 = true ↔ v1 = v2.
(* 
#A #n elim n
  [normalize #v1 #v2 % // #_ >(vector_nil … v1) >(vector_nil … v2) // 
  |#m #Hind #v1 #v2 
*)

definition DeqVector ≝ λA:DeqSet.λn.
  mk_DeqSet (Vector A n) (eq_Vector A n) (eq_Vector_true A n).

unification hint  0 ≔ C,n; 
    A ≟ carr C,
    X ≟ DeqVector C n
(* ---------------------------------------- *) ⊢ 
    Vector A n ≡ carr X.

unification hint  0 ≔ A,n,v1,v2; 
    X ≟ DeqVector A n
(* ---------------------------------------- *) ⊢ 
    eq_Vector A n v1 v2 ≡ eqb X v1 v2.

(* finset structure *)

let rec enum_vector A l n on n ≝ 
  match n with 
  [ O ⇒ [ ]
  | S n ⇒ foldr ?? (λi,acc.(map ?? (vec_cons A i n) (enum_vector A l n))@acc) [ ] l
  ].
  
axiom enum_vector_unique: ∀A,l,n. 
  uniqueb A l = true → uniqueb (DeqVector A n) (enum_vector A l n) = true.

axiom enum_vector_complete:∀A:DeqSet.∀l,n.
  (∀a. memb A a l = true) → 
    ∀v. memb ? v (enum_vector A l n) = true.

definition FinVector ≝ 
λA:FinSet.λn.mk_FinSet (DeqVector A n)
  (enum_vector A (enum A) n) 
  (enum_vector_unique A … (enum_unique A)) 
  (enum_vector_complete A … (enum_complete A)).

unification hint  0 ≔ C,n; 
    A ≟ FinSetcarr C,
    X ≟ FinVector C n
(* ---------------------------------------- *) ⊢ 
    Vector A n ≡ FinSetcarr X.

