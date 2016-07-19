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

include "pts_dummy_new/terms.ma".

(* to be put elsewhere *)
definition if_then_else ≝ λT:Type[0].λe,t,f.match e return λ_.T with [ true ⇒ t | false ⇒ f].

(* arguments: k is the depth (starts from 0), p is the height (starts from 0) *)
let rec lift t k p ≝
  match t with 
    [ Sort n ⇒ Sort n
    | Rel n ⇒ if_then_else T (leb k n) (Rel (n+p)) (Rel n)
    | App m n ⇒ App (lift m k p) (lift n k p)
    | Lambda m n ⇒ Lambda (lift m k p) (lift n (k+1) p)
    | Prod m n ⇒ Prod (lift m k p) (lift n (k+1) p)
    | D n m ⇒ D (lift n k p) (lift m k p) 
    ].

(* 
ndefinition lift ≝ λt.λp.lift_aux t 0 p.

notation "↑ ^ n ( M )" non associative with precedence 40 for @{'Lift O $M}.
notation "↑ _ k ^ n ( M )" non associative with precedence 40 for @{'Lift $n $k $M}.
*)
(* interpretation "Lift" 'Lift n M = (lift M n). *)
interpretation "Lift" 'Lift n k M = (lift M k n). 

let rec subst t k a ≝ 
  match t with 
    [ Sort n ⇒ Sort n
    | Rel n ⇒ if_then_else T (leb k n)
        (if_then_else T (eqb k n) (lift a 0 n) (Rel (n-1))) (Rel n)
    | App m n ⇒ App (subst m k a) (subst n k a)
    | Lambda m n ⇒ Lambda (subst m k a) (subst n (k+1) a)
    | Prod m n ⇒ Prod (subst m k a) (subst n (k+1) a)
    | D n m ⇒ D (subst n k a) (subst m k a) 
    ].

(* meglio non definire 
ndefinition subst ≝ λa.λt.subst_aux t 0 a.
notation "M [ N ]" non associative with precedence 90 for @{'Subst $N $M}.
*)

(* interpretation "Subst" 'Subst N M = (subst N M). *)
interpretation "Subst" 'Subst1 M k N = (subst M k N).

(*** properties of lift and subst ***)

lemma lift_0: ∀t:T.∀k. lift t k 0 = t.
#t (elim t) normalize // #n #k cases (leb k n) normalize // 
qed.

(* nlemma lift_0: ∀t:T. lift t 0 = t.
#t; nelim t; nnormalize; //; nqed. *)

lemma lift_sort: ∀i,k,n. lift (Sort i) k n = Sort i.
// qed.

lemma lift_rel: ∀i,n. lift (Rel i) 0 n = Rel (i+n).
// qed.

lemma lift_rel1: ∀i.lift (Rel i) 0 1 = Rel (S i).
#i (change with (lift (Rel i) 0 1 = Rel (1 + i))) //
qed.

lemma lift_rel_lt : ∀n,k,i. i < k → lift (Rel i) k n = Rel i.
#n #k #i #ltik change with 
(if_then_else ? (leb k i) (Rel (i+n)) (Rel i) = Rel i)
>(lt_to_leb_false … ltik) //
qed.

lemma lift_rel_ge : ∀n,k,i. k ≤ i → lift (Rel i) k n = Rel (i+n).
#n #k #i #leki change with 
(if_then_else ? (leb k i) (Rel (i+n)) (Rel i) = Rel (i+n))
>le_to_leb_true //
qed.

lemma lift_lift: ∀t.∀m,j.j ≤ m  → ∀n,k. 
  lift (lift t k m) (j+k) n = lift t k (m+n).
#t #i #j #h (elim t) normalize // #n #h #k
@(leb_elim k n) #Hnk normalize
  [>(le_to_leb_true (j+k) (n+i) ?)
     normalize // >(commutative_plus j k) @le_plus // 
  |>(lt_to_leb_false (j+k) n ?) normalize //
   @(transitive_le ? k) // @not_le_to_lt // 
  ]
qed.

lemma lift_lift_up: ∀n,m,t,k,i.
  lift (lift t i m) (m+k+i) n = lift (lift t (k+i) n) i m.
#n #m #N (elim N)
  [1,3,4,5,6: normalize //
  |#p #k #i @(leb_elim i p);
    [#leip >lift_rel_ge // @(leb_elim (k+i) p);
      [#lekip >lift_rel_ge; 
        [>lift_rel_ge // >lift_rel_ge // @(transitive_le … leip) //
        |>associative_plus >commutative_plus @monotonic_le_plus_l // 
        ]
      |#lefalse (cut (p < k+i)) [@not_le_to_lt //] #ltpki
       >lift_rel_lt; [|>associative_plus >commutative_plus @monotonic_lt_plus_r //] 
       >lift_rel_lt // >lift_rel_ge // 
      ]
    |#lefalse (cut (p < i)) [@not_le_to_lt //] #ltpi 
     >lift_rel_lt // >lift_rel_lt; [|@(lt_to_le_to_lt … ltpi) //]
     >lift_rel_lt; [|@(lt_to_le_to_lt … ltpi) //] 
     >lift_rel_lt //
    ]
  ]
qed.

lemma lift_lift1: ∀t.∀i,j,k. 
  lift(lift t k j) k i = lift t k (j+i).
/2/ qed.

lemma lift_lift2: ∀t.∀i,j,k. 
  lift (lift t k j) (j+k) i = lift t k (j+i).
/2/ qed.

(*
nlemma lift_lift: ∀t.∀i,j. lift (lift t j) i = lift t (j+i).
nnormalize; //; nqed. *)

lemma subst_lift_k: ∀A,B.∀k. (lift B k 1)[k ≝ A] = B.
#A #B (elim B) normalize /2/ #n #k
@(leb_elim k n) normalize #Hnk
  [cut (k ≤ n+1); [@transitive_le //] #H
   >(le_to_leb_true … H) normalize 
   >(not_eq_to_eqb_false k (n+1)) normalize /2/
  |>(lt_to_leb_false … (not_le_to_lt … Hnk)) normalize //
  ]
qed.

(*
nlemma subst_lift: ∀A,B. subst A (lift B 1) = B.
nnormalize; //; nqed. *)

lemma subst_sort: ∀A.∀n,k.(Sort n) [k ≝ A] = Sort n.
// qed.

lemma subst_rel: ∀A.(Rel 0) [0 ≝ A] = A.
normalize // qed.

lemma subst_rel1: ∀A.∀k,i. i < k → 
  (Rel i) [k ≝ A] = Rel i.
#A #k #i normalize #ltik >(lt_to_leb_false … ltik) //
qed.

lemma subst_rel2: ∀A.∀k. 
  (Rel k) [k ≝ A] = lift A 0 k.
#A #k normalize >(le_to_leb_true k k) // >(eq_to_eqb_true … (refl …)) //
qed.

lemma subst_rel3: ∀A.∀k,i. k < i → 
  (Rel i) [k ≝ A] = Rel (i-1).
#A #k #i normalize #ltik >(le_to_leb_true k i) /2/ 
>(not_eq_to_eqb_false k i) // @lt_to_not_eq //
qed.

lemma lift_subst_ijk: ∀A,B.∀i,j,k.
  lift (B [j+k := A]) k i = (lift B k i) [j+k+i ≝ A].
#A #B #i #j (elim B) normalize /2/ #n #k
@(leb_elim (j+k) n) normalize #Hnjk
  [@(eqb_elim (j+k) n) normalize #Heqnjk 
    [>(le_to_leb_true k n) // 
     (cut (j+k+i = n+i)) [//] #Heq
     >Heq >(subst_rel2 A ?) (applyS lift_lift) //
    |(cut (j + k < n))
      [@not_eq_to_le_to_lt; /2/] #ltjkn
     (cut (O < n)) [/2/] #posn (cut (k ≤ n)) [/2/] #lekn
     >(le_to_leb_true k (n-1)) normalize
      [>(le_to_leb_true … lekn)
       >(subst_rel3 A (j+k+i) (n+i)); [/3/ |/2/]
      |(applyS monotonic_pred) @le_plus_b //
      ]
    ]
  |(elim (leb k n)) 
    [>(subst_rel1 A (j+k+i) (n+i)) // @monotonic_lt_plus_l /2/
    |>(subst_rel1 A (j+k+i) n) // @(lt_to_le_to_lt ? (j+k)) /2/
    ]
  ]
qed.

lemma lift_subst_up: ∀M,N,n,i,j.
  lift M[i≝N] (i+j) n = (lift M (i+j+1) n)[i≝ (lift N j n)].
#M (elim M) 
  [//
  |#p #N #n #i #j (cases (true_or_false (leb p i)))
    [#lepi (cases (le_to_or_lt_eq … (leb_true_to_le … lepi)))
      [#ltpi >(subst_rel1 … ltpi) 
       (cut (p < i+j)) [@(lt_to_le_to_lt … ltpi) //] #ltpij
       >(lift_rel_lt … ltpij); >(lift_rel_lt ?? p ?); 
        [>subst_rel1 // | @(lt_to_le_to_lt … ltpij) //]
      |#eqpi >eqpi >subst_rel2 >lift_rel_lt;
        [>subst_rel2 >(plus_n_O (i+j)) 
         applyS lift_lift_up 
        |@(le_to_lt_to_lt ? (i+j)) //
        ]
      ]
    |#lefalse (cut (i < p)) [@not_le_to_lt /2/] #ltip
     (cut (0 < p)) [@(le_to_lt_to_lt … ltip) //] #posp
     >(subst_rel3 … ltip) (cases (true_or_false (leb (S p) (i+j+1))))
      [#Htrue (cut (p < i+j+1)) [@(leb_true_to_le … Htrue)] #Hlt
       >lift_rel_lt; 
        [>lift_rel_lt // >(subst_rel3 … ltip) // | @lt_plus_to_minus //]
      |#Hfalse >lift_rel_ge; 
        [>lift_rel_ge; 
          [>subst_rel3; [@eq_f /2/ | @(lt_to_le_to_lt … ltip) //]
          |@not_lt_to_le @(leb_false_to_not_le … Hfalse)
          ]
        |@le_plus_to_minus_r @not_lt_to_le 
         @(leb_false_to_not_le … Hfalse)
        ]
      ]
    ]
  |#P #Q #HindP #HindQ #N #n #i #j normalize 
   @eq_f2; [@HindP |@HindQ ]
  |#P #Q #HindP #HindQ #N #n #i #j normalize 
   @eq_f2; [@HindP |>associative_plus >(commutative_plus j 1)
   <associative_plus @HindQ]
  |#P #Q #HindP #HindQ #N #n #i #j normalize 
   @eq_f2; [@HindP |>associative_plus >(commutative_plus j 1)
   <associative_plus @HindQ]
  |#P #Q #HindP #HindQ #N #n #i #j normalize 
   @eq_f2; [@HindP |@HindQ ]
  ]
qed.

theorem delift : ∀A,B.∀i,j,k. i ≤ j → j ≤ i + k → 
  (lift B i (S k)) [j ≝ A] = lift B i k.
#A #B (elim B) normalize /2/
  [2,3,4,5: #T #T0 #Hind1 #Hind2 #i #j #k #leij #lejk
   @eq_f2 /2/ @Hind2 (applyS (monotonic_le_plus_l 1)) //
  |#n #i #j #k #leij #ltjk @(leb_elim i n) normalize #len
    [cut (j < n + S k);
      [<plus_n_Sm @le_S_S @(transitive_le … ltjk) /2/] #H
     >(le_to_leb_true j (n+S k));
      [normalize >(not_eq_to_eqb_false j (n+S k)) normalize /2/ 
      |/2/
      ]
    |>(lt_to_leb_false j n) // @(lt_to_le_to_lt … leij) 
     @not_le_to_lt //
    ]
  ]
qed.
     
(********************* substitution lemma ***********************)    

lemma subst_lemma: ∀A,B,C.∀k,i. 
  (A [i ≝ B]) [k+i ≝ C] = 
    (A [(k+i)+1:= C]) [i ≝ B [k ≝ C]].
#A #B #C #k (elim A) normalize // (* WOW *)
#n #i @(leb_elim i n) #Hle
  [@(eqb_elim i n) #eqni
    [<eqni >(lt_to_leb_false (k+i+1) i) // >(subst_rel2 …); 
     normalize @sym_eq (applyS (lift_subst_ijk C B i k O))
    |(cut (i < n)) 
      [cases (le_to_or_lt_eq … Hle) // #eqin @False_ind /2/] #ltin 
     (cut (O < n)) [@(le_to_lt_to_lt … ltin) //] #posn
     normalize @(leb_elim (k+i) (n-1)) #nk
      [@(eqb_elim (k+i) (n-1)) #H normalize
        [cut (k+i+1 = n); [/2/] #H1
         >(le_to_leb_true (k+i+1) n) /2/
         >(eq_to_eqb_true … H1) normalize 
         generalize in match ltin;
         @(lt_O_n_elim … posn) #m #leim >delift // /2/ 
        |(cut (k+i < n-1)) [@not_eq_to_le_to_lt; //] #Hlt 
         >(le_to_leb_true (k+i+1) n); 
          [>(not_eq_to_eqb_false (k+i+1) n);
            [>(subst_rel3 ? i (n-1));
             // @(le_to_lt_to_lt … Hlt) //
            |@(not_to_not … H) #Hn /2/ 
            ]
          |@le_minus_to_plus_r //  
          ]
        ]
      |>(not_le_to_leb_false (k+i+1) n);
        [>(subst_rel3 ? i n) normalize //
        |@(not_to_not … nk) #H @le_plus_to_minus_r //
        ]
      ]
    ]
  |(cut (n < k+i)) [@(lt_to_le_to_lt ? i) /2/] #ltn (* lento *) 
   (* (cut (n ≤ k+i)) [/2/] #len *)
   >(subst_rel1 C (k+i) n ltn) >(lt_to_leb_false (k+i+1) n);
    [>subst_rel1 /2/ | @(transitive_lt …ltn) // ]
  ] 
qed.
