(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_______________________________________________________________ *)

include "basics/lists/listb.ma".

(****** DeqSet: a set with a decidable equality ******)

record FinSet : Type[1] ≝ 
{ FinSetcarr:> DeqSet;
  enum: list FinSetcarr;
  enum_unique: uniqueb FinSetcarr enum = true;
  enum_complete : ∀x:FinSetcarr. memb ? x enum = true
}.

notation < "𝐅" non associative with precedence 90 
 for @{'bigF}.
interpretation "FinSet" 'bigF = (mk_FinSet ???).

(* bool *)
lemma bool_enum_unique: uniqueb ? [true;false] = true.
// qed.

lemma bool_enum_complete: ∀x:bool. memb ? x [true;false] = true.
* // qed.

definition FinBool ≝ 
  mk_FinSet DeqBool [true;false] bool_enum_unique bool_enum_complete.

unification hint  0 ≔ ; 
    X ≟ FinBool
(* ---------------------------------------- *) ⊢ 
    bool ≡ FinSetcarr X.

(* nat segment *)

lemma eqbnat_true : ∀n,m. eqb n m = true ↔ n = m.
#n #m % [@eqb_true_to_eq | @eq_to_eqb_true]
qed.

definition DeqNat ≝ mk_DeqSet nat eqb eqbnat_true.

lemma lt_to_le : ∀n,m. n < m → n ≤ m.
/2/ qed-.
 
let rec enumnaux n m ≝ 
  match n return (λn.n ≤ m → list (Σx.x < m)) with 
    [ O ⇒ λh.[ ] | S p ⇒ λh:p < m.(mk_Sig ?? p h)::enumnaux p m (lt_to_le p m h)].
    
definition enumn ≝ λn.enumnaux n n (le_n n).

definition Nat_to ≝ λn. DeqSig DeqNat (λi.i<n).

(* lemma prova : ∀n. carr (Nat_to n) = (Σx.x<n). // *)

lemma memb_enumn: ∀m,n,i:DeqNat. ∀h:n ≤ m. ∀k: i < m. n ≤ i →
  (¬ (memb (Nat_to m) (mk_Sig ?? i k) (enumnaux n m h))) = true.
#m #n elim n -n // #n #Hind #i #ltm #k #ltni @sym_eq @noteq_to_eqnot @sym_not_eq
% #H cases (orb_true_l … H)
  [whd in ⊢ (??%?→?); #H1 @(absurd  … ltni) @le_to_not_lt 
   >(eqb_true_to_eq … H1) @le_n
  |<(notb_notb (memb …)) >Hind normalize /2 by lt_to_le, absurd/
  ]
qed. 

lemma enumn_unique_aux: ∀n,m. ∀h:n ≤ m. uniqueb (Nat_to m) (enumnaux n m h) = true.
#n elim n -n // #n #Hind #m #h @true_to_andb_true // @memb_enumn //
qed.
 
lemma enumn_unique: ∀n.uniqueb (Nat_to n) (enumn n) = true.
#n @enumn_unique_aux
qed.

(* definition ltb ≝ λn,m.leb (S n) m. *)
lemma enumn_complete_aux: ∀n,m,i.∀h:n ≤m.∀k:i<m.i<n → 
  memb (Nat_to m) (mk_Sig ?? i k) (enumnaux n m h) = true.
#n elim n -n
  [normalize #n #i #_ #_ #Hfalse @False_ind /2/ 
  |#n #Hind #m #i #h #k #lein whd in ⊢ (??%?);
   cases (le_to_or_lt_eq … (le_S_S_to_le … lein))
    [#ltin cut (eqb (Nat_to m) (mk_Sig ?? i k) (mk_Sig ?? n h) = false)
      [normalize @not_eq_to_eqb_false @lt_to_not_eq @ltin] 
       #Hcut >Hcut @Hind //
    |#eqin cut (eqb (Nat_to m) (mk_Sig ?? i k) (mk_Sig ?? n h) = true)
     [normalize @eq_to_eqb_true //
     |#Hcut >Hcut %
    ]
  ]
qed.

lemma enumn_complete: ∀n.∀i:Nat_to n. memb ? i (enumn n) = true.
#n whd in ⊢ (%→?); * #i #ltin @enumn_complete_aux //
qed.

definition initN ≝ λn.
  mk_FinSet (Nat_to n) (enumn n) (enumn_unique n) (enumn_complete n).

example tipa: ∀n.∃x: initN (S n). pi1 … x = n.
#n @ex_intro [whd @mk_Sig [@n | @le_n] | //] qed.

(* option *)
definition enum_option ≝ λA:DeqSet.λl.
  None A::(map ?? (Some A) l).
  
lemma enum_option_def : ∀A:FinSet.∀l. 
  enum_option A l = None A :: (map ?? (Some A) l).
// qed.

lemma enum_option_unique: ∀A:DeqSet.∀l. 
  uniqueb A l = true → 
    uniqueb ? (enum_option A l) = true.
#A #l #uA @true_to_andb_true
  [generalize in match uA; -uA #_ elim l [%]
   #a #tl #Hind @sym_eq @noteq_to_eqnot % #H 
   cases (orb_true_l … (sym_eq … H))
    [#H1 @(absurd (None A = Some A a)) [@(\P H1) | % #H2 destruct]
    |-H #H >H in Hind; normalize /2/
    ]
  |@unique_map_inj // #a #a1 #H destruct %
  ]
qed.

lemma enum_option_complete: ∀A:DeqSet.∀l. 
  (∀x:A. memb A x l = true) →
    ∀x:DeqOption A. memb ? x (enum_option A l) = true.
#A #l #Hl * // #a @memb_cons @memb_map @Hl
qed.
    
definition FinOption ≝ λA:FinSet.
  mk_FinSet (DeqOption A) 
   (enum_option A (enum A)) 
   (enum_option_unique … (enum_unique A))
   (enum_option_complete … (enum_complete A)).

unification hint  0 ≔ C; 
    T ≟ FinSetcarr C,
    X ≟ FinOption C
(* ---------------------------------------- *) ⊢ 
    option T ≡ FinSetcarr X.

(* sum *)
definition enum_sum ≝ λA,B:DeqSet.λl1.λl2.
  (map ?? (inl A B) l1) @ (map ?? (inr A B) l2).
  
lemma enum_sum_def : ∀A,B:FinSet.∀l1,l2. enum_sum A B l1 l2 = 
  (map ?? (inl A B) l1) @ (map ?? (inr A B) l2).
// qed.

lemma enum_sum_unique: ∀A,B:DeqSet.∀l1,l2. 
  uniqueb A l1 = true → uniqueb B l2 = true → 
    uniqueb ? (enum_sum A B l1 l2) = true.
#A #B #l1 #l2 elim l1 
  [#_ #ul2 @unique_map_inj // #b1 #b2 #Hinr destruct //
  |#a #tl #Hind #uA #uB @true_to_andb_true 
    [@sym_eq @noteq_to_eqnot % #H 
     cases (memb_append … (sym_eq … H))
      [#H1 @(absurd (memb ? a tl = true)) 
        [@(memb_map_inj …H1) #a1 #a2 #Hinl destruct //
        |<(andb_true_l … uA) @eqnot_to_noteq //
        ]
      |elim l2
        [normalize #H destruct 
        |#b #tlB #Hind #membH cases (orb_true_l … membH)
          [#H lapply (\P H) #H1 destruct |@Hind]
        ]
      ] 
    |@Hind // @(andb_true_r … uA)
    ]
  ]
qed.

lemma enum_sum_complete: ∀A,B:DeqSet.∀l1,l2. 
  (∀x:A. memb A x l1 = true) →
  (∀x:B. memb B x l2 = true) →
    ∀x:DeqSum A B. memb ? x (enum_sum A B l1 l2) = true.
#A #B #l1 #l2 #Hl1 #Hl2 *
  [#a @memb_append_l1 @memb_map @Hl1
  |#b @memb_append_l2 @memb_map @Hl2
  ]
qed.
    
definition FinSum ≝ λA,B:FinSet.
  mk_FinSet (DeqSum A B) 
   (enum_sum A B (enum A) (enum B)) 
   (enum_sum_unique … (enum_unique A) (enum_unique B))
   (enum_sum_complete … (enum_complete A) (enum_complete B)).

include alias "basics/types.ma".

unification hint  0 ≔ C1,C2; 
    T1 ≟ FinSetcarr C1,
    T2 ≟ FinSetcarr C2,
    X ≟ FinSum C1 C2
(* ---------------------------------------- *) ⊢ 
    T1+T2 ≡ FinSetcarr X.

(* prod *)

definition enum_prod ≝ λA,B:DeqSet.λl1.λl2.
  compose ??? (mk_Prod A B) l1 l2.

lemma enum_prod_unique: ∀A,B,l1,l2. 
  uniqueb A l1 = true → uniqueb B l2 = true →
  uniqueb ? (enum_prod A B l1 l2) = true.
#A #B #l1 elim l1 //
  #a #tl #Hind #l2 #H1 #H2 @uniqueb_append 
  [@unique_map_inj [#x #y #Heq @(eq_f … \snd … Heq) | //]
  |@Hind // @(andb_true_r … H1)
  |#p #H3 cases (memb_map_to_exists … H3) #b * 
   #Hmemb #eqp <eqp @(not_to_not ? (memb ? a tl = true))
    [2: @sym_not_eq @eqnot_to_noteq @sym_eq @(andb_true_l … H1)
    |elim tl 
      [normalize //
      |#a1 #tl1 #Hind2 #H4 cases (memb_append … H4) -H4 #H4
        [cases (memb_map_to_exists … H4) #b1 * #memb1 #H destruct (H)
         normalize >(\b (refl ? a)) //
        |@orb_true_r2 @Hind2 @H4
        ]
      ]
    ]
  ]
qed.

lemma enum_prod_complete:∀A,B:DeqSet.∀l1,l2.
  (∀a. memb A a l1 = true) → (∀b.memb B b l2 = true) →
    ∀p. memb ? p (enum_prod A B l1 l2) = true.
#A #B #l1 #l2 #Hl1 #Hl2 * #a #b @memb_compose // 
qed.

definition FinProd ≝ 
λA,B:FinSet.mk_FinSet (DeqProd A B)
  (enum_prod A B (enum A) (enum B)) 
  (enum_prod_unique A B … (enum_unique A) (enum_unique B)) 
  (enum_prod_complete A B … (enum_complete A) (enum_complete B)).

unification hint  0 ≔ C1,C2; 
    T1 ≟ FinSetcarr C1,
    T2 ≟ FinSetcarr C2,
    X ≟ FinProd C1 C2
(* ---------------------------------------- *) ⊢ 
    T1×T2 ≡ FinSetcarr X.

(* graph of a function *)

definition graph_of ≝ λA,B.λf:A→B. 
  Σp:A×B.f (\fst p) = \snd p.

definition graph_enum ≝ λA,B:FinSet.λf:A→B. 
  filter ? (λp.f (\fst p) == \snd p) (enum (FinProd A B)).
  
lemma graph_enum_unique : ∀A,B,f.
  uniqueb ? (graph_enum A B f) = true.
#A #B #f @uniqueb_filter @(enum_unique (FinProd A B))
qed.

lemma graph_enum_correct: ∀A,B:FinSet.∀f:A→B. ∀a,b.
memb ? 〈a,b〉 (graph_enum A B f) = true → f a = b.
#A #B #f #a #b #membp @(\P ?) @(filter_true … membp)
qed.

lemma graph_enum_complete: ∀A,B:FinSet.∀f:A→B. ∀a,b.
f a = b → memb ? 〈a,b〉 (graph_enum A B f) = true.
#A #B #f #a #b #eqf @memb_filter_l [@(\b eqf)]
@enum_prod_complete //
qed.
