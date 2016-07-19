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

definition injn: (nat → nat) → nat → Prop ≝ λf,n.∀i,j:nat. 
  i ≤ n → j ≤ n → f i = f j → i = j.

theorem injn_Sn_n: ∀f,n. injn f (S n) → injn f n.
#f #n #H #i #j #lei #lej #eqf @H [@le_S // |@le_S //|//] 
qed.

theorem injective_to_injn: ∀f,n. injective nat nat f → injn f n.
#f #n #Hinj #i #j #_ #_ #eqf @Hinj // 
qed.

definition permut : (nat → nat) → nat → Prop 
≝ λf,m.(∀i.i ≤ m → f i ≤ m )∧ injn f m.

theorem permut_O_to_eq_O: ∀h.permut h O → h O = O.
#h * #H1 #_ @sym_eq @le_n_O_to_eq @H1 //
qed.

theorem permut_S_to_permut: ∀f,m.
  permut f (S m) → f (S m) = (S m) → permut f m.
#f #m * #H1 #H2 #Hf %
  [#i #leim cases(le_to_or_lt_eq … (H1 … (le_S … leim)))
    [#H @le_S_S_to_le @H
    |#H @False_ind @(absurd ? leim) @lt_to_not_le
     lapply Hf <H in ⊢ (???%→?); -H #H <(H2 … H) // @le_S //
    ]
  |#i #j #lei #lej #eqf @H2 [@le_S //|@le_S // |//]
  ]
qed.

(* transpositions *)

definition transpose : nat → nat → nat → nat ≝ λi,j,n:nat. 
  if eqb n i then j else if eqb n j then i else n.

(*
notation < "(❲i↹j❳) term 72 n" with precedence 71 
for @{ 'transposition $i $j $n}.

notation "(❲i \atop j❳) term 72 n" with precedence 71 
for @{ 'transposition $i $j $n}.

notation > "(❲\frac term 90 i term 90 j❳)n" with precedence 71 
for @{ 'transposition $i $j $n}.
*)

interpretation "natural transposition" 'transposition i j n = (transpose i j n).

lemma transpose_i_j_i: ∀i,j. transpose i j i = j.
#i #j normalize >(eqb_n_n i) // 
qed.

lemma transpose_i_j_j: ∀i,j. transpose i j j = i.
#i #j normalize cases(true_or_false (eqb j i)) #Hc 
  [>Hc normalize >(eqb_true_to_eq … Hc) //  
  |>Hc >(eqb_n_n j) //
  ]
qed.

theorem transpose_i_i:  ∀i,n:nat. (transpose  i i n) = n.
#i #n normalize cases (true_or_false (eqb n i)) #Hc >Hc
  [normalize >(eqb_true_to_eq … Hc) // |// ]
qed.

theorem transpose_i_j_j_i: ∀i,j,n:nat.
transpose i j n = transpose j i n.
#i #j #n normalize cases (true_or_false (eqb n i)) #Hni >Hni
cases (true_or_false (eqb n j)) #Hnj >Hnj normalize //
<(eqb_true_to_eq … Hni) <(eqb_true_to_eq … Hnj) //
qed.

theorem transpose_transpose: ∀i,j,n:nat.
  (transpose i j (transpose i j n)) = n.
#i #j #n normalize cases (true_or_false (eqb n i)) #Hni >Hni normalize
  [cases (true_or_false (eqb j i)) #Hji >Hji normalize
    [>(eqb_true_to_eq … Hni) @(eqb_true_to_eq … Hji) 
    |>(eqb_n_n j) normalize @sym_eq @(eqb_true_to_eq … Hni)
    ]
  |cases (true_or_false (eqb n j)) #Hnj >Hnj normalize
    [>(eqb_n_n i) normalize @sym_eq @(eqb_true_to_eq … Hnj)
    |>Hni >Hnj //
    ]
  ]
qed.

theorem injective_transpose : ∀i,j:nat. 
  injective nat nat (transpose i j).
// qed.

theorem permut_transpose: ∀i,j,n. i ≤ n → j ≤ n → permut (transpose i j) n.
#i #j #n #lein #lejn %
  [#a #lean normalize cases (eqb a i) cases (eqb a j) normalize //
  |#a #b #lean #lebn @(injective_to_injn (transpose i j) n) //
  ]
qed.

theorem permut_fg: ∀f,g,n.
  permut f n → permut g n → permut (λm.(f(g m))) n.
#f #g #n * #permf1 #permf2 * #permg1 #permg2 %
  [#i #lein @permf1 @permg1 @lein
  |#a #b #lean #lebn #Heq @permg2 // @permf2 
    [@permg1 @lean |@permg1 @lebn | //]
  ]
qed.   

theorem permut_transpose_l: ∀f,m,i,j.i ≤ m → j ≤ m → 
  permut f m → permut (λn.transpose i j (f n)) m.  
#f #m #i #j #leim #lejm #permf @(permut_fg … permf) @permut_transpose // 
qed.

theorem permut_transpose_r: ∀f,m,i,j. i ≤ m → j ≤ m → 
  permut f m → permut (λn.f (transpose i j n)) m.  
#f #m #i #j #leim #lejm #permf @(permut_fg … permf) @permut_transpose // 
qed.

theorem eq_transpose : ∀i,j,k,n:nat. j≠i → i≠k → j≠k →
  transpose i j n = transpose i k (transpose k j (transpose i k n)).
#i #j #k #n #Hji #Hik #Hjk normalize
cases (true_or_false (eqb n i)) #Hni >Hni normalize
  [>(eqb_n_n k) normalize >(not_eq_to_eqb_false … Hji) 
   >(not_eq_to_eqb_false … Hjk) % 
  |cases (true_or_false (eqb n k)) #Hnk >Hnk normalize
    [>(not_eq_to_eqb_false n j)
      [2: @(not_to_not …Hjk) <(eqb_true_to_eq … Hnk) //]
     >(not_eq_to_eqb_false … Hik) >(not_eq_to_eqb_false … i j)
      [2: @(not_to_not … Hji) //] 
     normalize >(eqb_n_n i) @(eqb_true_to_eq … Hnk)
    |>Hnk normalize
     cases (true_or_false (eqb n j)) #Hnj >Hnj normalize
      [>(not_eq_to_eqb_false k i)[2: @(not_to_not … Hik) //] 
       normalize >(eqb_n_n k) %
      |>Hni >Hnk %
      ]
    ]
  ]
qed. 

theorem permut_S_to_permut_transpose: ∀f,m.
  permut f (S m) → permut (λn.transpose (f (S m)) (S m) (f n)) m.
#f #m * #permf1 #permf2 %
  [#i #leim normalize >(not_eq_to_eqb_false (f i) (f (S m))) normalize
    [2: % #H @(absurd … (i= S m)) 
      [@(permf2 … H) [@le_S //|//]  |@lt_to_not_eq @le_S_S //]
    ]
   cases(le_to_or_lt_eq … (permf1 … (le_S … leim))) #Hfi
    [>(not_eq_to_eqb_false (f i) (S m)) [2:@lt_to_not_eq //]
     normalize @le_S_S_to_le @Hfi
    |>(eq_to_eqb_true …Hfi) normalize
     cases(le_to_or_lt_eq … (permf1 … (le_n (S m)))) #H
      [@le_S_S_to_le @H 
      |@False_ind @(absurd (i= S m))
        [@permf2 [@le_S // | //| //]
        |@(not_to_not ? (S m ≤ m)) [// |@lt_to_not_le //]
        ]
      ]
    ]
  |#a #b #leam #lebm #H @permf2 
    [@le_S //|@le_S //| @(injective_transpose … H)]
  ]
qed.
        
(* bounded bijectivity *)

definition bijn : (nat → nat) → nat → Prop ≝
λf,n.∀m:nat. m ≤ n → ex nat (λp. p ≤ n ∧ f p = m).

theorem eq_to_bijn:  ∀f,g,n.
  (∀i.i ≤ n → f i = g i) →  bijn f n → bijn g n.
#f #g #n #H #bijf #i #lein cases (bijf … lein) #a * #lean #fa
%{a} % // <fa @sym_eq @H //
qed.

theorem bijn_Sn_n: ∀f,n.
  bijn f (S n) → f (S n) = S n → bijn f n.
#f #n #bijf #fS #i #lein cases (bijf … (le_S … lein)) #a * #lean #fa
cases (le_to_or_lt_eq … lean) #Hc
  [%{a} % [@le_S_S_to_le @Hc |@fa]
  |@False_ind @(absurd ?? (not_le_Sn_n n)) <fS //
  ]
qed.

theorem bijn_n_Sn: ∀f,n.
  bijn f n → f (S n) = S n → bijn f (S n).
#f #n #bijf #fS #i #lein
cases (le_to_or_lt_eq … lein) #Hi
  [cases (bijf … (le_S_S_to_le … Hi)) #a * #lean #fa 
   %{a} % [@le_S //|//]
  |%{i} % //
  ]
qed.

theorem bijn_fg: ∀f,g:nat→ nat.∀n:nat.
  bijn f n → bijn g n → bijn (λp.f(g p)) n.
#f #g #n #bijf #bijg #i #lein cases (bijf … lein) #a * #lean #ga
cases (bijg … lean) #b * #lebn #gb %{b} % //
qed.

(*
theorem bijn_to_injn: ∀f,n. bijn f n → injn f n.
#f #n normalize #H #i #j #lein #lejn #eqf 
cases (H … lein) #a * #lean #fa
cases (H … lejn) #b * #lebn #fb
cases (bijg … lean) #b * #lebn #gb %{b} % //
qed.
*)

theorem bijn_transpose : ∀n,i,j. i ≤ n → j ≤ n →
  bijn (transpose i j) n.
#n #i #j #lein #lejn #a #lean
cases (true_or_false (eqb a i)) #Hi
  [%{j} % // >transpose_i_j_j @sym_eq @(eqb_true_to_eq … Hi)
  |cases (true_or_false (eqb a j)) #Hj 
    [%{i} % // >transpose_i_j_i @sym_eq @(eqb_true_to_eq … Hj)
    |%{a} % // normalize >Hi >Hj %
    ]
  ]
qed.  

theorem bijn_transpose_r: ∀f,n,i,j. i ≤ n → j ≤ n →
  bijn f n → bijn (λp.f (transpose i j p)) n.
#f #n #i #j #lein #lejn #bijf @(bijn_fg f ?) /2/
qed.

theorem bijn_transpose_l: ∀f,n,i,j. i ≤ n → j ≤ n →
  bijn f n → bijn (λp.transpose i j (f p)) n.
#f #n #i #j #lein #lejn #bijf @(bijn_fg ? f) /2/
qed.

theorem permut_to_bijn: ∀n,f. permut f n → bijn f n.
#n elim n 
  [#f normalize * #H #H1 #m #lem0 %{0} % // 
   @(le_n_O_elim … lem0) @sym_eq @le_n_O_to_eq @H //
  |#m #Hind #f #permf 
   @(eq_to_bijn (λp.
      (transpose (f (S m)) (S m)) (transpose (f (S m)) (S m) (f p))) f)
    [#i #lei @transpose_transpose
    |@(bijn_fg (transpose (f (S m)) (S m)))
      [cases permf #lef #_ @bijn_transpose [@lef // |//]
      |@bijn_n_Sn 
        [@Hind @permut_S_to_permut_transpose //
        |normalize >(eqb_n_n (f (S m))) % 
        ]
      ]
    ]
  ]
qed.

let rec invert_permut n f m ≝
  match eqb m (f n) with
  [true ⇒ n
  |false ⇒ 
     match n with
     [O ⇒ O
     |(S p) ⇒ invert_permut p f m]].

theorem invert_permut_f: ∀f:nat → nat. ∀n,m:nat.
  m ≤ n → injn f n → invert_permut n f (f m) = m.
#f #n #m #lenm elim lenm
  [cases m normalize [>(eqb_n_n (f O)) //| #a >(eqb_n_n (f (S a))) //]
  |#m0 #lem #H #H1 normalize 
   >(not_eq_to_eqb_false (f m) (f (S m0))) 
    [@H @injn_Sn_n //
    |% #eqf @(absurd (m = S m0)) 
      [@H1 [@le_S // |//|//] |@lt_to_not_eq @le_S_S //]
    ]
  ]
qed.

theorem injective_invert_permut: ∀f,n.
  permut f n → injn (invert_permut n f) n.
#f #n #permf #i #j #lein #lejn lapply (permut_to_bijn … permf) #bijf
cases (bijf i lein) #a * #lean #fa
cases (bijf j lejn) #b * #lebn #fb
cases permf #_ #injf
<fa <fb >(invert_permut_f … lean injf) >(invert_permut_f … lebn injf) //
qed. 

theorem permut_invert_permut: ∀f,n.
  permut f n → permut (invert_permut n f) n.
#f #n #permf % 
  [#i #lein elim n normalize 
    [cases (eqb i (f O)) %
    |#n1 #Hind cases (eqb i (f (S n1))) [@le_n | normalize @le_S //]
    ]
  |@injective_invert_permut //
  ]
qed.

theorem f_invert_permut: ∀f,n,m.
  m ≤ n → permut f n → f (invert_permut n f m) = m.
#f #n #m #lemn #permf lapply (permut_invert_permut … permf)
* #Hle #Hinj cases permf #lef #injf @(injective_invert_permut … permf … lemn)
  [@lef @Hle //
  |@invert_permut_f [@Hle //| //]
  ]
qed.

theorem permut_n_to_eq_n: ∀h,n.
  permut h n → (∀m:nat. m < n → h m = m) → h n = n.
#h #n #permh cases permh #leh #injh #eqh 
lapply (permut_invert_permut … permh) * #Hle #Hinj
cases (le_to_or_lt_eq … (Hle … (le_n n))) #Hc
  [<(f_invert_permut … (le_n n) permh) in ⊢ (???%); @eq_f
   <(f_invert_permut … (le_n n) permh) in ⊢ (??%?); @eqh @Hc
  |<Hc in ⊢ (??%?); @(f_invert_permut h) //
  ]
qed.

theorem permut_n_to_le: ∀h,k,n.
k ≤ n → permut h n → (∀m.m < k → h m = m) → 
  ∀j. k ≤ j → j ≤ n → k ≤ h j.
#h #k #n #lekn * #leh #injh #H #j #lekj #lejn 
cases (decidable_lt (h j) k) #Hh
  [@False_ind @(absurd … lekj) @lt_to_not_le
   cut (h j = j) 
    [@injh [@(transitive_le … lekn) @lt_to_le // |@lejn|@H //]] #Hj 
   <Hj //
  |@not_lt_to_le //
  ]
qed.
