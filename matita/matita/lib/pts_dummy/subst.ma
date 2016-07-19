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

include "pts_dummy/lift.ma".
(*
let rec subst t k a ≝ 
  match t with 
    [ Sort n ⇒ Sort n
    | Rel n ⇒ if_then_else T (leb (S n) k) (Rel n)
        (if_then_else T (eqb n k) (lift a 0 n) (Rel (n-1)))
    | App m n ⇒ App (subst m k a) (subst n k a)
    | Lambda m n ⇒ Lambda (subst m k a) (subst n (k+1) a)
    | Prod m n ⇒ Prod (subst m k a) (subst n (k+1) a)
    | D n ⇒ D (subst n k a)
    ].

(* meglio non definire 
ndefinition subst ≝ λa.λt.subst_aux t 0 a.
notation "M [ N ]" non associative with precedence 90 for @{'Subst $N $M}.
*)

(* interpretation "Subst" 'Subst N M = (subst N M). *)
interpretation "Subst" 'Subst1 M k N = (subst M k N).

(*** properties of subst ***)

lemma subst_lift_k: ∀A,B.∀k. (lift B k 1)[k ≝ A] = B.
#A #B (elim B) normalize /2/ #n #k
@(leb_elim (S n) k) normalize #Hnk
  [>(le_to_leb_true ?? Hnk) normalize //
  |>(lt_to_leb_false (S (n + 1)) k ?) normalize
    [>(not_eq_to_eqb_false (n+1) k ?) normalize /2/
    |@le_S (applyS (not_le_to_lt (S n) k Hnk))
    ]
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
#A #k #i normalize #ltik >(le_to_leb_true (S i) k) //
qed.

lemma subst_rel2: ∀A.∀k. 
  (Rel k) [k ≝ A] = lift A 0 k.
#A #k normalize >(lt_to_leb_false (S k) k) // >(eq_to_eqb_true … (refl …)) //
qed.

lemma subst_rel3: ∀A.∀k,i. k < i → 
  (Rel i) [k ≝ A] = Rel (i-1).
#A #k #i normalize #ltik >(lt_to_leb_false (S i) k) /2/ 
>(not_eq_to_eqb_false i k) // @sym_not_eq @lt_to_not_eq //
qed.

lemma lift_subst_ijk: ∀A,B.∀i,j,k.
  lift (B [j+k := A]) k i = (lift B k i) [j+k+i ≝ A].
#A #B #i #j (elim B) normalize /2/ #n #k
@(leb_elim (S n) (j + k)) normalize #Hnjk
  [(elim (leb (S n) k))
    [>(subst_rel1 A (j+k+i) n) /2/
    |>(subst_rel1 A (j+k+i) (n+i)) /2/
    ]
  |@(eqb_elim n (j+k)) normalize #Heqnjk 
    [>(lt_to_leb_false (S n) k);
      [(cut (j+k+i = n+i)) [//] #Heq
       >Heq >(subst_rel2 A ?) normalize (applyS lift_lift) //
      |/2/
      ]
    |(cut (j + k < n))
      [@not_eq_to_le_to_lt;
        [/2/ |@le_S_S_to_le @not_le_to_lt /2/ ]
      |#ltjkn
       (cut (O < n)) [/2/] #posn (cut (k ≤ n)) [/2/] #lekn
       >(lt_to_leb_false (S (n-1)) k) normalize
        [>(lt_to_leb_false … (le_S_S … lekn))
         >(subst_rel3 A (j+k+i) (n+i)); [/3/ |/2/]
        |@le_S_S; (* /3/; 65 *) (applyS monotonic_pred) @le_plus_b //
        ]
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
  |#P #HindP #N #n #i #j normalize 
   @eq_f @HindP
  ]
qed.

lemma lift_subst_up_O: ∀v,t,k,p. (lift t (k+1) p)[O≝lift v k p] = lift t[O≝v] k p.
// qed.

theorem delift : ∀A,B.∀i,j,k. i ≤ j → j ≤ i + k → 
  (lift B i (S k)) [j ≝ A] = lift B i k.
#A #B (elim B) normalize /2/
  [2,3,4: #T #T0 #Hind1 #Hind2 #i #j #k #leij #lejk
   @eq_f2 /2/ @Hind2 (applyS (monotonic_le_plus_l 1)) //
  |5:#T #Hind #i #j #k #leij #lejk @eq_f @Hind //
  |#n #i #j #k #leij #ltjk @(leb_elim (S n) i) normalize #len
    [>(le_to_leb_true (S n) j) /2/
    |>(lt_to_leb_false (S (n+S k)) j);
      [normalize >(not_eq_to_eqb_false (n+S k) j)normalize 
       /2/ @(not_to_not …len) #H @(le_plus_to_le_r k) normalize //
      |@le_S_S @(transitive_le … ltjk) @le_plus // @not_lt_to_le /2/
      ]
    ]
  ]
qed.
     
(********************* substitution lemma ***********************)    

lemma subst_lemma: ∀A,B,C.∀k,i. 
  (A [i ≝ B]) [k+i ≝ C] = 
    (A [S (k+i) := C]) [i ≝ B [k ≝ C]].
#A #B #C #k (elim A) normalize // (* WOW *)
#n #i @(leb_elim (S n) i) #Hle
  [(cut (n < k+i)) [/2/] #ltn (* lento *) (cut (n ≤ k+i)) [/2/] #len
   >(subst_rel1 C (k+i) n ltn) >(le_to_leb_true n (k+i) len) >(subst_rel1 … Hle) // 
  |@(eqb_elim n i) #eqni
    [>eqni >(le_to_leb_true i (k+i)) // >(subst_rel2 …); 
     normalize @sym_eq (applyS (lift_subst_ijk C B i k O))
    |@(leb_elim (S (n-1)) (k+i)) #nk
      [>(subst_rel1 C (k+i) (n-1) nk) >(le_to_leb_true n (k+i));
        [>(subst_rel3 ? i n) // @not_eq_to_le_to_lt;
          [/2/ |@not_lt_to_le /2/]
        |@(transitive_le … nk) //
        ]
      |(cut (i < n)) [@not_eq_to_le_to_lt; [/2/] @(not_lt_to_le … Hle)]
       #ltin (cut (O < n)) [/2/] #posn
       @(eqb_elim (n-1) (k+i)) #H
        [>H >(subst_rel2 C (k+i)) >(lt_to_leb_false n (k+i));
          [>(eq_to_eqb_true n (S(k+i))); 
            [normalize |<H (applyS plus_minus_m_m) // ]
           (generalize in match ltin)
           <H @(lt_O_n_elim … posn) #m #leim >delift normalize /2/
          |<H @(lt_O_n_elim … posn) #m normalize //
          ]
        |(cut (k+i < n-1))
          [@not_eq_to_le_to_lt; [@sym_not_eq @H |@(not_lt_to_le … nk)]]
         #Hlt >(lt_to_leb_false n (k+i));
          [>(not_eq_to_eqb_false n (S(k+i)));
            [>(subst_rel3 C (k+i) (n-1) Hlt);
             >(subst_rel3 ? i (n-1)) // @(le_to_lt_to_lt … Hlt) //
            |@(not_to_not … H) #Hn >Hn normalize //
            ]
          |@(transitive_lt … Hlt) @(lt_O_n_elim … posn) normalize // 
          ]
        ]
      ]
    ]
  ] 
qed.

lemma subst_lemma_comm: ∀A,B,C.∀k,i.
  (A [i ≝ B]) [i+k ≝ C] = (A [i+k+1 := C]) [i ≝ B [k ≝ C]].
#A #B #C #k #i >commutative_plus >subst_lemma //
qed. 
*)
