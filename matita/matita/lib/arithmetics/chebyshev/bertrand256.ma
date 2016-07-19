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

include "arithmetics/chebyshev/bertrand.ma".
include "basics/lists/list.ma".

let rec list_divides l n ≝
  match l with
  [ nil ⇒ false
  | cons (m:nat) (tl:list nat) ⇒ orb (dividesb m n) (list_divides tl n) ].
  
lemma list_divides_true: ∀l,n. list_divides l n = true → ∃p. mem ? p l ∧ p ∣ n.
#l elim l 
  [#n normalize in ⊢ (%→?); #H destruct (H)
  |#a #tl #Hind #b cases (true_or_false (dividesb a b)) #Hcase
    [#_ %{a} % [% // | @dividesb_true_to_divides //]
    |whd in ⊢ (??%?→?); >Hcase whd in ⊢ (??%?→?); #Htl
     cases (Hind b Htl) #d * #memd #divd %{d} % [%2 // | //]
    ]
  ]
qed.

lemma list_divides_false: ∀l,n. list_divides l n = false → 
  ∀p. mem ? p l → p \ndivides  n.
#l elim l 
  [#n #_ #p normalize in ⊢ (%→?); @False_ind
  |#a #tl #Hind #b cases (true_or_false (dividesb a b)) #Hcase
    [whd in ⊢ (??%?→?); >Hcase whd in ⊢ (??%?→?);
     #H destruct (H)
    |whd in ⊢ (??%?→?); >Hcase whd in ⊢ (??%?→?); #Htl #d * 
      [#eqda >eqda @dividesb_false_to_not_divides //
      |#memd @Hind // 
      ]
    ]
  ]
qed.

let rec lprim m i acc ≝
  match m with 
   [ O ⇒  acc
   | S m1 ⇒  match (list_divides acc i) with
     [ true ⇒  lprim m1 (S i) acc
     | false ⇒ lprim m1 (S i) (acc@[i]) ]].
     
definition list_of_primes ≝ λn. lprim n 2 [].

lemma lop_Strue: ∀m,i,acc. list_divides acc i =true → 
  lprim (S m) i acc = lprim m (S i) acc.
#m #i #acc #Hdiv normalize >Hdiv //
qed.

lemma lop_Sfalse: ∀m,i,acc. list_divides acc i = false → 
  lprim (S m) i acc = lprim m (S i) (acc@[i]).
#m #i #acc #Hdiv normalize >Hdiv %
qed.

lemma list_of_primes_def : ∀n. list_of_primes n = lprim n 2 [].
// qed.

example lprim_ex: lprim 8 2 [ ] = [2; 3; 5; 7]. // qed.

lemma start_lprim: ∀n,m,a,acc.
  option_hd ? (lprim n m (a::acc)) = Some ? a.
#n elim n 
  [#m #a #acc % 
  |#n1 #Hind #m #a #acc cases (true_or_false (list_divides (a::acc) m)) #Hc
    [>lop_Strue [@Hind | //] |>lop_Sfalse [@Hind |//]
  ]
qed.

lemma start_lop: ∀n. 1 ≤ n →
  option_hd ? (list_of_primes n) = Some ? 2.
#n #posn cases posn //
  #m #lem >list_of_primes_def normalize in ⊢ (??(??%)?);
  >start_lprim //
qed.

lemma eq_lop: ∀n. 1 ≤ n → 
  list_of_primes n = 2::(tail ? (list_of_primes n)).
#n #posn lapply (start_lop ? posn) cases (list_of_primes n)
  [whd in ⊢ (??%?→?); #H destruct (H)
  |normalize #a #l #H destruct (H) //
  ]
qed.


(* properties *)

definition all_primes ≝ λl.∀p. mem nat p l → prime p.

definition all_below ≝ λl,n.∀p. mem nat p l → p < n.

definition primes_all ≝ λl,n. ∀p. prime p → p < n → mem nat p l.

definition primes_below ≝ λl,n.
  all_primes l ∧ all_below l n ∧ primes_all l n.

lemma ld_to_prime: ∀i,acc. 1 < i →
  primes_below acc i → list_divides acc i = false → prime i.
#i #acc #posi * * #Hall #Hbelow #Hcomplete #Hfalse % // 
#m #mdivi 
cut (m ≤ i)[@divides_to_le [@lt_to_le //|//]] #lemi
cases (le_to_or_lt_eq … lemi) [2://] #ltmi
#lt1m @False_ind
cut (divides (smallest_factor m) i) 
  [@(transitive_divides … mdivi) @divides_smallest_factor_n @lt_to_le //]
#Hcut @(absurd … Hcut) @(list_divides_false … Hfalse) @Hcomplete
  [@prime_smallest_factor_n // | @(le_to_lt_to_lt … ltmi) //]
qed.

lemma lprim_invariant: ∀n,i,acc. 1 < i →
  primes_below acc i → primes_below (lprim n i acc) (n+i).
#n elim n
  [#i #acc #lt1i #H @H 
  |#m #Hind #i #acc #lt1i * * #Hall #Hbelow #Hcomplete cases (true_or_false (list_divides acc i)) #Hc
    [>(lop_Strue … Hc) whd in ⊢ (??%); >plus_n_Sm @(Hind … (le_S … lt1i)) %
      [% [// |#p #memp @le_S @Hbelow //]
      |#p #primep #lepi cases (le_to_or_lt_eq … (le_S_S_to_le … lepi))
        [#ltpi @Hcomplete // 
        |#eqpi @False_ind cases (list_divides_true … Hc) #q * #memq #divqi
         cases primep #lt1p >eqpi #Hi @(absurd (q=i))
          [@Hi [@divqi |@prime_to_lt_SO @Hall //]
          |@lt_to_not_eq @Hbelow //
          ]
        ]
      ]
    |>(lop_Sfalse … Hc) whd in ⊢ (??%); >plus_n_Sm @(Hind … (le_S … lt1i)) %
      [% [#p #memp cases (mem_append ???? memp) -memp #memp
           [@Hall //|>(mem_single ??? memp) @(ld_to_prime … Hc) // % [% // |//]]
      |#p #memp cases (mem_append ???? memp) -memp #memp
         [@le_S @Hbelow // |<(mem_single ??? memp) @le_n]]
      |#p #memp #ltp cases (le_to_or_lt_eq … (le_S_S_to_le … ltp))
         [#ltpi @mem_append_l1 @Hcomplete //|#eqpi @mem_append_l2 <eqpi % //]
      ]
    ]
  ]
qed.
       
lemma primes_below2: primes_below [] 2.
  %[%[#p @False_ind|#p @False_ind] 
   |#p #primep #ltp2 @False_ind @(absurd … ltp2) @le_to_not_lt
    @prime_to_lt_SO //
   ]
qed.

lemma primes_below_lop: ∀n. primes_below (list_of_primes n) (n+2).
#n @lprim_invariant //
qed.

(* check *)
theorem primes_below_to_bertrand: 
∀pm,l.prime pm → primes_below l (S pm)  →
  (∀p. mem ? p l → 2 < p → ∃pp. mem ? pp l ∧ pp < p ∧ p ≤ 2*pp) 
    → ∀n.0 < n → n < pm → bertrand n.
#pm #l #primepm * * #Hall #Hbelow #Hcomplete #H #n #posn #ltn  
cases (min_prim n) #p1 * * #ltnp1 #primep1 #Hmin
%{p1} % // % [//] 
cases(le_to_or_lt_eq ? ? (prime_to_lt_SO ? primep1)) #Hp1
  [cases (H … Hp1)
    [#x * * #memxl #ltxp1 #Hp1 @(transitive_le … Hp1) @monotonic_le_times_r 
     @Hmin [@Hall //|//]
    |@Hcomplete [//] @le_S_S @not_lt_to_le % #ltpm @(absurd ? ltn)
     @le_to_not_lt @Hmin //
    ]
  |<Hp1 >(times_n_1 2) in ⊢ (?%?); @monotonic_le_times_r //
  ]
qed.

let rec checker l ≝
  match l with
  [ nil ⇒ true
  | cons hd tl ⇒
    match tl with
     [ nil ⇒ true
     | cons hd1 tl1 ⇒ 
       leb (S hd) hd1 ∧ leb hd1 (2*hd) ∧ checker tl
    ]
  ].

lemma checker_ab: ∀a,b,l.checker (a::b::l) =
  (leb (S a) b ∧ leb b (2*a) ∧ checker (b::l)).
// qed.

lemma checker_abl: ∀a,b,l.checker (a::b::l) = true →
  a < b ∧ b ≤ 2*a ∧ checker (b::l) = true.
#a #b #l >checker_ab #H 
% [% [@leb_true_to_le @(andb_true_l … (andb_true_l … H))
     |@leb_true_to_le @(andb_true_r … (andb_true_l … H))
     ]
  |@(andb_true_r … H)
  ]
qed.
    
theorem checker_spec: ∀tl,a,l. checker l = true → l = a::tl →
  ∀p. mem ? p tl → ∃pp. mem nat pp l ∧ pp < p ∧ p ≤ 2*pp.
#tl elim tl
  [#a #l #_ #_ #p whd in ⊢ (%→?); @False_ind 
  |#b #tl #Hind #a #l #Hc #Hl #p #Hmem >Hl in Hc;
   #Hc cases(checker_abl … Hc) *  
   #ltab #leb #Hc2 cases Hmem #Hc
    [>Hc -Hc %{a} % [ % [ % % |//]|//]
    |cases(Hind b (b::tl) Hc2 (refl …) ? Hc) #pp * * #Hmemnp #ltpp #lepp
     %{pp} % [ % [ %2 //|//]|//]
    ]
  ]
qed.

lemma bertrand_down : ∀n.O < n → n ≤ 2^8 → bertrand n.
#n #posn #len
cut (∃it.it=2^8) [%{(2^8)} %] * #it #itdef
lapply(primes_below_lop … it) * * #Hall #Hbelow #Hcomplete
@(primes_below_to_bertrand (S it) (list_of_primes it) … posn)
  [@primeb_true_to_prime >itdef %
  |>(plus_n_O it) in ⊢ (??%); >plus_n_Sm >plus_n_Sm @primes_below_lop
  |#p #memp #lt2p @(checker_spec (tail ? (list_of_primes it)) 2 (list_of_primes it))
    [>itdef %
    |>itdef @eq_lop @lt_O_S 
    |>eq_lop in memp; [2:>itdef @lt_O_S] * 
      [#eqp2 @False_ind @(absurd ? lt2p) @le_to_not_lt >eqp2 @le_n
      |#H @H
      ]
    ]
  |@le_S_S >itdef @len
  ]
qed.

theorem bertrand :
∀n. O < n → bertrand n.
#n #posn elim (decidable_le n 256)
  [@bertrand_down //
  |#len @bertrand_up @lt_to_le @not_le_to_lt @len]
qed.

