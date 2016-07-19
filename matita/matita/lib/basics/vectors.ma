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

include "basics/lists/list.ma".

record Vector (A:Type[0]) (n:nat): Type[0] ≝ 
{ vec :> list A;
  len: length ? vec = n
}.

lemma Vector_of_list ≝ λA,l. 
  mk_Vector A (|l|) l (refl ??).

lemma Vector_eq : ∀A,n,v1,v2.
  vec A n v1 = vec A n v2 → v1 = v2.
#A #n * #l1 #H1 * #l2 #H2 #eql1l2 generalize in match H1; 
-H1 >eql1l2 //
qed.

definition vec_tail ≝ λA.λn.λv:Vector A n.
mk_Vector A (pred n) (tail A v) ?.
>length_tail >(len A n v) //
qed.

definition vec_cons ≝ λA.λa.λn.λv:Vector A n.
mk_Vector A (S n) (cons A a v) ?.
normalize >(len A n v) //
qed.

definition vec_hd ≝ λA.λn.λv:Vector A (S n).
hd A v ?. elim v * [normalize #H destruct | #a #H #eq @a] 
qed.

lemma vec_expand: ∀A,n,v. 
 v = vec_cons A (vec_hd A n v) n (vec_tail A (S n) v).
#A #n * #l cases l [normalize in ⊢ (%→?); #H destruct  |//]
qed.

lemma vector_nil: ∀A.∀v:Vector A 0. 
  v = mk_Vector A 0 (nil A) (refl ??).
#A * * // #a #tl normalize #H destruct
qed. 

definition vec_append ≝ λA.λn1,n2.λv1:Vector A n1.λv2: Vector A n2.
mk_Vector A (n1+n2) (v1@v2).

definition vec_map ≝ λA,B.λf:A→B.λn.λv:Vector A n.
mk_Vector B n (map ?? f v) 
  (trans_eq … (length_map …) (len A n v)).
  
lemma nth_default : ∀A,i,n.∀v:Vector A n.∀d1,d2. i < n →
  nth i ? v d1 = nth i ? v d2.
#A #i elim i -i
  [#n #v #d1 #d2 #ltOn lapply v @(lt_O_n_elim … ltOn)
   -v #m #v >(vec_expand … v) //
  |#i #Hind #n #v #d1 #d2 #ltn lapply ltn lapply v @(lt_O_n_elim … (ltn_to_ltO … ltn))
   -v -ltn #m #v #ltim >(vec_expand … v) @(Hind m (vec_tail A (S m) v) d1 d2 ?) 
   @le_S_S_to_le //
  ]
qed.
  
lemma eq_vec: ∀A,n.∀v1,v2:Vector A n.∀d. 
  (∀i. i < n → nth i A v1 d = nth i A v2 d) → v1 = v2.
#A #n elim n -n 
  [#v1 #v2 #H >(vector_nil A v1) >(vector_nil A v2) //
  |#n #Hind #v1 #v2 #d #H >(vec_expand … v1) >(vec_expand … v2)
   >(Hind (vec_tail … v1) (vec_tail … v2) d)
    [cut (vec_hd A n v1 = vec_hd A n v2) //
     cut (∀i,d1,d2. i < S n → nth i A v1 d1 = nth i A v2 d2)
       [#i #d1 #d2 #Hi >(nth_default ????? d) // >(nth_default ???? d2 d) // @H //]
     -H #H @(H 0) //  
    |#i #ltin @(H (S i)) @le_S_S //
    ]
  ]
qed.

lemma nth_vec_map :
  ∀A,B,f,i,n.∀v:Vector A n.∀d.
  f (nth i ? v d) = nth i ? (vec_map A B f n v) (f d).
#A #B #f #i elim i
[ *
  [ #v #d >(vector_nil … v) %
  | #n0 #v #d >(vec_expand … v) % ]
| #i0 #IH *
  [ #v #d >(vector_nil … v) normalize cases i0 // 
  | #n #v #d >(vec_expand … v) whd in ⊢ (??(?%)%);
    >(IH n (vec_tail A (S n) v) d) % ] ]
qed.


(* mapi: map with index to move in list.ma *)
let rec change_vec (A:Type[0]) (n:nat) on n ≝
match n return λn0.∀v:Vector A n0.A→nat→Vector A n0 with
[ O ⇒ λv,a,i.v
| S m ⇒ λv,a,i.
  match i with
  [ O ⇒ vec_cons A a m (vec_tail … v) 
  | S j ⇒ vec_cons A (vec_hd A m v) m (change_vec A m (vec_tail … v) a j)
  ]
].

lemma nth_change_vec : ∀A,i,n,v,a,d. i < n →
  nth i ? (change_vec A n v a i) d = a.
#A #i elim i
  [#n #v #a #d #ltOn lapply v -v @(lt_O_n_elim n ltOn ??) //
  |#m #Hind #n #v #a #d #Hlt 
   lapply Hlt lapply v @(lt_O_n_elim … (ltn_to_ltO … Hlt)) 
   #p #v #ltmp @Hind @le_S_S_to_le // 
  ]
qed.

lemma nth_change_vec_neq : ∀A,j,i,n,v,a,d. i ≠ j →
  nth j ? (change_vec A n v a i) d = nth j ? v d.
#A #j elim j
  [#i * // #n #v #a #d cases i
    [#H @False_ind @(absurd ?? H) //
    |#i0 #_ >(vec_expand ?? v) in ⊢ (???%); //
    ] 
  |#m #Hind #i * // cases i // #i0 #n #v #a #d #neqim 
   whd in ⊢(??%?); whd in match (tail ??); >Hind
    [>(vec_expand ??v) in ⊢ (???%); // |@(not_to_not … neqim) // ]
  ]
qed.

lemma change_vec_same : ∀sig,n,v,i,d.
  change_vec sig n v (nth i ? v d) i = v.
#sig #n #v #i #d @(eq_vec … d)
#i0 #Hi0 cases (decidable_eq_nat i i0) #Hi0
[ >Hi0 >nth_change_vec //
| >nth_change_vec_neq //
]
qed.

lemma change_vec_cons_tail :∀A,n,vA,a,b,i.
  change_vec A (S n) (vec_cons ? a n vA) b (S i) =
  vec_cons ? a n (change_vec A n vA b i).
#A #n #vA cases vA //
qed.

lemma change_vec_commute : ∀A,n,v,a,b,i,j. i ≠ j → 
  change_vec A n (change_vec A n v a i) b j
  = change_vec A n (change_vec A n v b j) a i.
#A #n #v #a #b #i #j #Hij @(eq_vec … a)
#k #Hk cases (decidable_eq_nat k i) #Hki
[ >Hki >nth_change_vec // >(nth_change_vec_neq ??????? (sym_not_eq … Hij))
  >nth_change_vec //
| cases (decidable_eq_nat k j) #Hkj
  [ >Hkj >nth_change_vec // >(nth_change_vec_neq ??????? Hij) >nth_change_vec //
  | >(nth_change_vec_neq ??????? (sym_not_eq … Hki))
    >(nth_change_vec_neq ??????? (sym_not_eq … Hkj))
    >(nth_change_vec_neq ??????? (sym_not_eq … Hki))
    >(nth_change_vec_neq ??????? (sym_not_eq … Hkj)) //
  ]
]
qed.

lemma change_vec_change_vec : ∀A,n,v,a,b,i. 
  change_vec A n (change_vec A n v a i) b i = change_vec A n v b i.
#A #n #v #a #b #i @(eq_vec … a) #i0 #Hi0
cases (decidable_eq_nat i i0) #Hii0
[ >Hii0 >nth_change_vec // >nth_change_vec //
| >nth_change_vec_neq // >nth_change_vec_neq //
  >nth_change_vec_neq // ]
qed.

lemma eq_vec_change_vec : ∀sig,n.∀v1,v2:Vector sig n.∀i,t,d.
  nth i ? v2 d = t → 
  (∀j.i ≠ j → nth j ? v1 d = nth j ? v2 d) → 
  v2 = change_vec ?? v1 t i.
#sig #n #v1 #v2 #i #t #d #H1 #H2 @(eq_vec … d)
#i0 #Hlt cases (decidable_eq_nat i0 i) #Hii0
[ >Hii0 >nth_change_vec //
| >nth_change_vec_neq [|@sym_not_eq //] @sym_eq @H2 @sym_not_eq // ]
qed-.

(* map *) 

let rec pmap A B C (f:A→B→C) l1 l2 on l1 ≝
   match l1 with
   [ nil ⇒ nil C
   | cons a tlA ⇒ 
     match l2 with
     [nil ⇒ nil C
     |cons b tlB ⇒ (f a b)::pmap A B C f tlA tlB
     ]
   ].

lemma length_pmap: ∀A,B,C.∀f:A→B→C.∀l1,l2.
length C (pmap  A B C f l1 l2) = 
  min (length A l1) (length B l2).
#A #B #C #f #l1 elim l1 // #a #tlA #Hind #l2 cases l2 //
#b #tlB lapply (Hind tlB) normalize 
cases (true_or_false (leb (length A tlA) (length B tlB))) #H >H
normalize //
qed.

definition pmap_vec ≝ λA,B,C.λf:A→B→C.λn.λvA:Vector A n.λvB:Vector B n.
mk_Vector C n (pmap A B C f vA vB) ?.
>length_pmap >(len A n vA) >(len B n vB) normalize 
>(le_to_leb_true … (le_n n)) //
qed.

lemma pmap_vec_cons :∀A,B,C,f,n,vA,vB,a,b.
  pmap_vec A B C f (S n) (vec_cons ? a n vA) (vec_cons ? b n vB) =
  vec_cons ? (f a b) n (pmap_vec A B C f n vA vB).
// qed.

lemma pmap_change : ∀A,B,C,f,n,vA,vB,a,b,i.
  pmap_vec A B C f n (change_vec ? n vA a i) (change_vec ? n vB b i) =
  change_vec ? n (pmap_vec A B C f n vA vB) (f a b) i.
#A #B #C #f #n elim n //
#m #Hind #vA #vB #a #b >(vec_expand … vA) >(vec_expand … vB) * //
#i >pmap_vec_cons >pmap_vec_cons >change_vec_cons_tail @eq_f @Hind 
qed.