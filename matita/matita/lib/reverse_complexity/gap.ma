
include "arithmetics/minimization.ma".
include "arithmetics/bigops.ma".
include "arithmetics/pidgeon_hole.ma".
include "arithmetics/iteration.ma".

(************************** notation for miminimization ***********************)

(* an alternative defintion of minimization 
definition Min ≝ λa,f. 
  \big[min,a]_{i < a | f i} i. *)

notation "μ_{ ident i < n } p" 
  with precedence 80 for @{min $n 0 (λ${ident i}.$p)}.

notation "μ_{ ident i ≤ n } p" 
  with precedence 80 for @{min (S $n) 0 (λ${ident i}.$p)}.
  
notation "μ_{ ident i ∈ [a,b] } p"
  with precedence 80 for @{min (S $b-$a) $a (λ${ident i}.$p)}.
  
lemma f_min_true: ∀f,a,b.
  (∃i. a ≤ i ∧ i ≤ b ∧ f i = true) → f (μ_{i ∈[a,b]} (f i)) = true.
#f #a #b * #i * * #Hil #Hir #Hfi @(f_min_true … (λx. f x)) <plus_minus_m_m 
  [%{i} % // % [@Hil |@le_S_S @Hir]|@le_S @(transitive_le … Hil Hir)]
qed.

lemma min_up: ∀f,a,b.
  (∃i. a ≤ i ∧ i ≤ b ∧ f i = true) → μ_{i ∈[a,b]}(f i) ≤ b. 
#f #a #b * #i * * #Hil #Hir #Hfi @le_S_S_to_le
cut ((S b) = S b - a + a) [@plus_minus_m_m @le_S @(transitive_le … Hil Hir)]
#Hcut >Hcut in ⊢ (??%); @lt_min %{i} % // % [@Hil |<Hcut @le_S_S @Hir]
qed.

(*************************** Kleene's predicate *******************************)

axiom U: nat → nat →nat → option nat.

axiom monotonic_U: ∀i,x,n,m,y.n ≤m →
  U i x n = Some ? y → U i x m = Some ? y.
  
lemma unique_U: ∀i,x,n,m,yn,ym.
  U i x n = Some ? yn → U i x m = Some ? ym → yn = ym.
#i #x #n #m #yn #ym #Hn #Hm cases (decidable_le n m)
  [#lenm lapply (monotonic_U … lenm Hn) >Hm #HS destruct (HS) //
  |#ltmn lapply (monotonic_U … n … Hm) [@lt_to_le @not_le_to_lt //]
   >Hn #HS destruct (HS) //
  ]
qed.

definition terminate ≝ λi,x,r. ∃y. U i x r = Some ? y.

notation "〈i,x〉 ↓ r" with precedence 60 for @{terminate $i $x $r}.

lemma terminate_dec: ∀i,x,n. 〈i,x〉 ↓ n ∨ ¬ 〈i,x〉 ↓ n.
#i #x #n normalize cases (U i x n)
  [%2 % * #y #H destruct|#y %1 %{y} //]
qed. 

definition termb ≝ λi,x,t. 
  match U i x t with [None ⇒ false |Some y ⇒ true].

lemma termb_true_to_term: ∀i,x,t. termb i x t = true → 〈i,x〉 ↓ t.
#i #x #t normalize cases (U i x t) normalize [#H destruct | #y #_ %{y} //]
qed.    

lemma term_to_termb_true: ∀i,x,t. 〈i,x〉 ↓ t → termb i x t = true.
#i #x #t * #y #H normalize >H // 
qed.    

lemma decidable_test : ∀n,x,r,r1.
       (∀i. i < n → 〈i,x〉 ↓ r ∨ ¬ 〈i,x〉 ↓ r1) ∨ 
       (∃i. i < n ∧ (¬ 〈i,x〉 ↓ r ∧ 〈i,x〉 ↓ r1)).
#n #x #r1 #r2
  cut (∀i0.decidable ((〈i0,x〉↓r1) ∨ ¬ 〈i0,x〉 ↓ r2)) 
    [#j @decidable_or [@terminate_dec |@decidable_not @terminate_dec ]] #Hdec
 cases(decidable_forall ? Hdec n) 
  [#H %1 @H  
  |#H %2 cases (not_forall_to_exists … Hdec H) #j * #leji #Hj
   %{j} % // % 
    [@(not_to_not … Hj) #H %1 @H 
    |cases (terminate_dec j x r2) // #H @False_ind cases Hj -Hj #Hj
     @Hj %2 @H
  ]
qed.

(**************************** the gap theorem *********************************)
definition gapP ≝ λn,x,g,r. ∀i. i < n → 〈i,x〉 ↓ r ∨ ¬ 〈i,x〉 ↓ g r.

lemma gapP_def : ∀n,x,g,r. 
  gapP n x g r = ∀i. i < n → 〈i,x〉 ↓ r ∨ ¬ 〈i,x〉 ↓ g r.
// qed.

lemma upper_bound_aux: ∀g,b,n,x. (∀x. x ≤ g x) → ∀k.
  (∃j.j < k ∧
    (∀i. i < n → 〈i,x〉 ↓ g^j b ∨ ¬ 〈i,x〉 ↓ g^(S j) b)) ∨
  ∃l. |l| = k ∧ unique ? l ∧ ∀i. i ∈ l → i < n ∧ 〈i,x〉 ↓ g^k b .
#g#b #n #x #Hg #k elim k 
  [%2 %{([])} normalize % [% //|#x @False_ind]
  |#k0 * 
    [* #j * #lej #H %1 %{j} % [@le_S // | @H ]
    |* #l * * #Hlen #Hunique #Hterm
     cases (decidable_test n x (g^k0 b) (g^(S k0) b))
      [#Hcase %1 %{k0} % [@le_n | @Hcase]
      |* #j * #ltjn * #H1 #H2 %2 
       %{(j::l)} % 
        [ % [normalize @eq_f @Hlen] whd % // % #H3
         @(absurd ?? H1) @(proj2 … (Hterm …)) @H3
        |#x *
          [#eqxj >eqxj % // 
          |#Hmemx cases(Hterm … Hmemx) #lexn * #y #HU
           % [@lexn] %{y} @(monotonic_U ?????? HU) @Hg
          ]
        ]
      ]
    ]
  ]
qed.
       
lemma upper_bound: ∀g,b,n,x. (∀x. x ≤ g x) → ∃r. 
  (* b ≤ r ∧ r ≤ g^n b ∧ ∀i. i < n → 〈i,x〉 ↓ r ∨ ¬ 〈i,x〉 ↓ g r. *)
  b ≤ r ∧ r ≤ g^n b ∧ gapP n x g r. 
#g #b #n #x #Hg 
cases (upper_bound_aux g b n x Hg n)
  [* #j * #Hj #H %{(g^j b)} % [2: @H] % [@le_iter //]
   @monotonic_iter2 // @lt_to_le //
  |* #l * * #Hlen #Hunique #Hterm %{(g^n b)} % 
    [% [@le_iter // |@le_n]] 
   #i #lein %1 @(proj2 … (Hterm ??)) 
   @(eq_length_to_mem_all … Hlen Hunique … lein)
   #x #memx @(proj1  … (Hterm ??)) //
  ]
qed. 

definition gapb ≝ λn,x,g,r.
  \big[andb,true]_{i < n} ((termb i x r) ∨ ¬(termb i x (g r))). 
  
lemma gapb_def : ∀n,x,g,r. gapb n x g r =
  \big[andb,true]_{i < n} ((termb i x r) ∨ ¬(termb i x (g r))). 
// qed.

lemma gapb_true_to_gapP : ∀n,x,g,r. 
  gapb n x g r = true → ∀i. i < n → 〈i,x〉 ↓ r ∨ ¬(〈i,x〉 ↓ (g r)).
#n #x #g #r elim n 
  [>gapb_def >bigop_Strue //
   #H #i #lti0 @False_ind @(absurd … lti0) @le_to_not_lt //
  |#m #Hind >gapb_def >bigop_Strue //
   #H #i #leSm cases (le_to_or_lt_eq … leSm)
    [#lem @Hind [@(andb_true_r … H)|@le_S_S_to_le @lem]
    |#eqi >(injective_S … eqi) lapply (andb_true_l … H) -H #H cases (orb_true_l … H) -H
      [#H %1 @termb_true_to_term //
      |#H %2 % #H1 >(term_to_termb_true …  H1) in H; normalize #H destruct
      ]
    ]
  ]
qed.

lemma gapP_to_gapb_true : ∀n,x,g,r. 
  (∀i. i < n → 〈i,x〉 ↓ r ∨ ¬(〈i,x〉 ↓ (g r))) → gapb n x g r = true. 
#n #x #g #r elim n //
#m #Hind #H >gapb_def >bigop_Strue // @true_to_andb_true
  [cases (H m (le_n …)) 
    [#H2 @orb_true_r1 @term_to_termb_true //
    |#H2 @orb_true_r2 @sym_eq @noteq_to_eqnot @sym_not_eq 
     @(not_to_not … H2) @termb_true_to_term 
    ]
  |@Hind #i0 #lei0 @H @le_S //
  ]
qed.


(* the gap function *)
let rec gap g n on n ≝
  match n with 
  [ O ⇒ 1
  | S m ⇒ let b ≝ gap g m in μ_{i ∈ [b,g^n b]} (gapb n n g i)
  ].
  
lemma gapS: ∀g,m. 
  gap g (S m) = 
    (let b ≝ gap g m in 
      μ_{i ∈ [b,g^(S m) b]} (gapb (S m) (S m) g i)).
// qed.

lemma upper_bound_gapb: ∀g,m. (∀x. x ≤ g x) → 
  ∃r:ℕ.gap g m ≤ r ∧ r ≤ g^(S m) (gap g m) ∧ gapb (S m) (S m) g r = true.
#g #m #leg 
lapply (upper_bound g (gap g m) (S m) (S m) leg) * #r * *
#H1 #H2 #H3 %{r} % 
  [% // |@gapP_to_gapb_true @H3]
qed.
   
lemma gapS_true: ∀g,m. (∀x. x ≤g x) → gapb (S m) (S m) g (gap g (S m)) = true.
#g #m #leg @(f_min_true (gapb (S m) (S m) g)) @upper_bound_gapb //
qed.
  
theorem gap_theorem: ∀g,i.(∀x. x ≤ g x)→∃k.∀n.k < n → 
   〈i,n〉 ↓ (gap g n) ∨ ¬ 〈i,n〉 ↓ (g (gap g n)).
#g #i #leg %{i} * 
  [#lti0 @False_ind @(absurd ?? (not_le_Sn_O i) ) //
  |#m #leim lapply (gapS_true g m leg) #H
   @(gapb_true_to_gapP … H) //
  ]
qed.

(* an upper bound *)

let rec sigma n ≝ 
  match n with 
  [ O ⇒ 0 | S m ⇒ n + sigma m ].
  
lemma gap_bound: ∀g. (∀x. x ≤ g x) → (monotonic ? le g) → 
  ∀n.gap g n ≤ g^(sigma n) 1.
#g #leg #gmono #n elim n 
  [normalize //
  |#m #Hind >gapS @(transitive_le ? (g^(S m) (gap g m)))
    [@min_up @upper_bound_gapb // 
    |@(transitive_le ? (g^(S m) (g^(sigma m) 1)))
      [@monotonic_iter // |>iter_iter >commutative_plus @le_n
    ]
  ]
qed.

lemma gap_bound2: ∀g. (∀x. x ≤ g x) → (monotonic ? le g) → 
  ∀n.gap g n ≤ g^(n*n) 1.
#g #leg #gmono #n elim n 
  [normalize //
  |#m #Hind >gapS @(transitive_le ? (g^(S m) (gap g m)))
    [@min_up @upper_bound_gapb // 
    |@(transitive_le ? (g^(S m) (g^(m*m) 1)))
      [@monotonic_iter //
      |>iter_iter @monotonic_iter2 [@leg | normalize <plus_n_Sm @le_S_S //
    ]
  ]
qed.

(*
axiom universal: ∃u.∀i,x,y. 
  ∃n. U u 〈i,x〉 n = Some y ↔ ∃m.U i x m = Some y. *)

   










