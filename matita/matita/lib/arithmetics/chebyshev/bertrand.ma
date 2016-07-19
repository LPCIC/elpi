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

include "arithmetics/sqrt.ma".
include "arithmetics/chebyshev/psi_bounds.ma". 
include "arithmetics/chebyshev/chebyshev_theta.ma". 

definition bertrand ≝ λn. ∃p.n < p ∧ p ≤ 2*n ∧ prime p.

definition not_bertrand ≝ λn.∀p.n < p → p ≤ 2*n → ¬(prime p).

lemma min_prim : ∀n.∃p. n < p ∧ prime p ∧
                 ∀q.prime q → q < p → q ≤ n.
#n cases (le_to_or_lt_eq ?? (le_O_n n)) #Hn
  [%{(min (S (n!)) (S n) primeb)} %
    [%[@le_min_l
      |@primeb_true_to_prime @(f_min_true primeb)
       cases (ex_prime n Hn) #p * * #ltnp #lep #primep
       %{p} % 
        [% [@ltnp | whd >(plus_n_O p) >plus_n_Sm @le_plus //]
        |@prime_to_primeb_true //
        ]
      ]
    |#p #primep #ltp @not_lt_to_le % #ltnp 
     lapply (lt_min_to_false … ltnp ltp)
     >(prime_to_primeb_true ? primep) #H destruct (H)
    ]
  |%{2} % 
    [%[<Hn @lt_O_S | @primeb_true_to_prime //]
    |#p #primep #lt2 @False_ind @(absurd … lt2)
     @le_to_not_lt @prime_to_lt_SO //
    ]
  ]
qed.

lemma not_not_bertrand_to_bertrand1: ∀n.
¬(not_bertrand n) → ∀x. n ≤ x → x ≤ 2*n →
  (∀p.x < p → p ≤ 2*n → ¬(prime p))
  → ∃p.n < p ∧ p ≤ x ∧ (prime p).
#n #not_not #x #lenx elim lenx  
  [#len #Bn @False_ind @(absurd ?? not_not) @Bn 
  |#n1 #lenn1 #Hind #ltn1 #HB cases (true_or_false (primeb (S n1))) #Hc
    [%{(S n1)} % [% [@le_S_S // |//] |@primeb_true_to_prime // ]
    |cases (Hind ??) 
      [#p * * #ltnp #lep #primep %{p} %[%[@ltnp|@le_S//]|//]
      |@lt_to_le //
      |#p #ltp #lep cases (le_to_or_lt_eq ?? ltp) #Hcase
        [@HB // |<Hcase @primeb_false_to_not_prime //]
      ]
    ]
  ]
qed.
  
theorem not_not_bertrand_to_bertrand: ∀n.
  ¬(not_bertrand n) → bertrand n.
#n #not_not @(not_not_bertrand_to_bertrand1 ?? (2*n)) //
#p #le2n #lep @False_ind @(absurd ? le2n) @le_to_not_lt //
qed.

definition k ≝ λn,p. 
  ∑_{i < log p n}((n/(exp p (S i))\mod 2)).
  
lemma k_def : ∀n,p. k n p = ∑_{i < log p n}((n/(exp p (S i))\mod 2)).
// qed.

theorem le_k: ∀n,p. k n p ≤ log p n.
#n #p >k_def elim (log p n)
  [@le_n
  |#n1 #Hind >bigop_Strue
    [>(plus_n_O n1) in ⊢ (??%); >plus_n_Sm >commutative_plus
     @le_plus
      [@Hind 
      |@le_S_S_to_le @lt_mod_m_m @lt_O_S 
      ]
    |//
    ]
  ]
qed.

definition Bk ≝ λn. 
  ∏_{p < S n | primeb p}(exp p (k n p)).
  
lemma Bk_def : ∀n. Bk n = ∏_{p < S n | primeb p}(exp p (k n p)).
// qed.

definition Dexp ≝ mk_Dop nat 1 timesAC (λa,b.exp b a) ??.
  [// | normalize //]
qed.
  
theorem eq_B_Bk: ∀n. B n = Bk n.
#n >Bdef >Bk_def @same_bigop
  [// |#i #ltiS #_ >k_def @exp_sigma_l]
qed.

definition B1 ≝ λn. 
  ∏_{p < S n | primeb p}(exp p (bool_to_nat (leb (k n p) 1)* (k n p))).

lemma B1_def : ∀n.
  B1 n = ∏_{p < S n | primeb p}(exp p (bool_to_nat (leb (k n p) 1)* (k n p))).
// qed.

definition B2 ≝ λn. 
  ∏_{p < S n | primeb p}(exp p (bool_to_nat (leb 2 (k n p))* (k n p))).

lemma B2_def : ∀n.
  B2 n = ∏_{p < S n | primeb p}(exp p (bool_to_nat (leb 2 (k n p))* (k n p))).
// qed.

theorem eq_Bk_B1_B2: ∀n. 
  Bk n = B1 n * B2 n.
#n >Bk_def >B1_def >B2_def <times_pi
@same_bigop
  [//
  |#p #ltp #primebp cases (true_or_false (leb (k n p) 1)) #Hc >Hc
    [>(lt_to_leb_false 2 (k n p))
      [<times_n_1 >commutative_times <times_n_1 //
      |@le_S_S @leb_true_to_le //
      ]
    |>(le_to_leb_true 2 (k n p))
      [>commutative_times <times_n_1 >commutative_times <times_n_1 //
      |@not_le_to_lt @leb_false_to_not_le //
      ]
    ]
  ]
qed.

lemma lt_div_to_times: ∀n,m,q. O < q → n/q < m → n < q*m.
#n #m #q #posq #ltm
cut (O < m) [@(ltn_to_ltO …  ltm)] #posm
@not_le_to_lt % #len @(absurd …ltm) @le_to_not_lt @le_times_to_le_div //
qed.

(* integrare in div_and_mod *)
lemma lt_to_div_O:∀n,m. n < m → n / m = O.
#n #m #ltnm @(div_mod_spec_to_eq n m (n/m) (n \mod m) O n)
  [@div_mod_spec_div_mod @(ltn_to_ltO ?? ltnm)
  |@div_mod_spec_intro //
  ]
qed.

(* the value of n could be smaller *) 
lemma k1: ∀n,p. 18 ≤ n → p ≤ n → 2*n/ 3 < p → k (2*n) p = O.
#n #p #le18 #lep #ltp >k_def
elim (log p (2*n))
  [//
  |#i #Hind >bigop_Strue 
    [>Hind <plus_n_O cases i
      [<exp_n_1
       cut (2*n/p = 2) [2:#Hcut >Hcut //]
       @lt_to_le_times_to_lt_S_to_div
        [@(ltn_to_ltO ?? ltp)
        |<commutative_times @monotonic_le_times_r //
        |>commutative_times in ⊢ (??%); @lt_div_to_times //
        ]
      |#n2 cut (2*n/(p)\sup(S (S n2)) = O) [2:#Hcut >Hcut //]
       @lt_to_div_O @(le_to_lt_to_lt ? (exp ((2*n)/3) 2))
        [@(le_times_to_le (exp 3 2))
          [@leb_true_to_le //
          |>commutative_times in ⊢ (??%); > times_exp
           @(transitive_le ? (exp n 2))
            [<associative_times >exp_2 in ⊢ (??%); @le_times [@le18|//]
            |@(le_exp1 … (lt_O_S ?))
             @(le_plus_to_le 3)
             cut (3+2*n/3*3 = S(2*n/3)*3) [//] #eq1 >eq1
             @(transitive_le ? (2*n))
              [normalize in ⊢(??%); <plus_n_O
               @monotonic_le_plus_l @(transitive_le ? 18 … le18)
               @leb_true_to_le //
              |@lt_to_le @lt_div_S @lt_O_S
              ]
            ]
          ]
        |@(lt_to_le_to_lt ? (exp p 2))
          [@lt_exp1 [@lt_O_S|//]
          |@le_exp [@(ltn_to_ltO ?? ltp) |@le_S_S @le_S_S @le_O_n]
          ]
        ]
      ]
    |//
    ]
  ]
qed.
        
theorem le_B1_theta:∀n.18 ≤ n → not_bertrand n →
  B1 (2*n) ≤ theta (2 * n / 3).
#n #le18 #not_Bn >B1_def >theta_def
@(transitive_le ? (∏_{p < S (2*n) | primeb p} (p\sup(bool_to_nat (eqb (k (2*n) p) 1)))))
  [@le_pi #p #ltp #primebp @le_exp
    [@prime_to_lt_O @primeb_true_to_prime //
    |cases (true_or_false (leb (k (2*n) p) 1)) #Hc 
      [cases (le_to_or_lt_eq ? ? (leb_true_to_le ?? Hc)) -Hc #Hc
        [lapply (le_S_S_to_le ?? Hc) -Hc #Hc
         @(le_n_O_elim ? Hc) <times_n_O @le_n
        |>(eq_to_eqb_true ?? Hc) >Hc @le_n
        ]
      |>Hc @le_O_n
      ]
    ]
  |@(transitive_le ? (∏_{p < S (2*n/3) | primeb p} (p\sup(bool_to_nat (eqb (k (2*n) p) 1)))))
    [>(pad_bigop_nil (S(2*n)) (S (2*n/3)) primeb ? 1 timesA) [//]
      [#i #lei #lti whd in not_Bn;
       cases (decidable_le (S n) i) #Hc
        [%1 @not_prime_to_primeb_false @not_Bn [//|@le_S_S_to_le //]
        |%2 >k1 // @not_lt_to_le @Hc
        ]
      |@le_S_S @le_times_to_le_div2
        [@lt_O_S
        |>commutative_times in ⊢ (??%); @le_times //
        ]
      ]
    |@le_pi #i #lti #primei cases (eqb (k (2*n) i) 1)
      [<exp_n_1 @le_n
      |normalize @prime_to_lt_O @primeb_true_to_prime //
      ]
    ]
  ]
qed.

theorem le_B2_exp: ∀n. exp 2 7 ≤ n →
  B2 (2*n) ≤ exp (2*n) (pred(sqrt(2*n)/2)).
#n #len >B2_def
cut (O < n) [@(lt_to_le_to_lt … len) @leb_true_to_le //] #posn
@(transitive_le ? 
   (∏_{p < S (sqrt (2*n)) | primeb p}
      (p\sup(bool_to_nat (leb 2 (k (2*n) p))*k (2*n) p))))
  [>(pad_bigop_nil (S (2*n)) (S(sqrt(2*n))) primeb ? 1 timesA) 
    [//|3: @le_S_S @le_sqrt_n]
   #p #lep #ltp cases (true_or_false (leb 2 (k (2*n) p))) #Hc
    [@False_ind @(absurd ?? (lt_to_not_le ?? lep))
     @(true_to_le_max … ltp) @le_to_leb_true <exp_2
     @not_lt_to_le % #H2n 
     @(absurd ?? (le_to_not_lt 2 (log p (2*n)) ?))
      [@le_S_S @f_false_to_le_max
        [%{0} % 
          [>(times_n_1 0) in ⊢ (?%?); >commutative_times in ⊢ (?%?);
           @lt_times //
          |@le_to_leb_true @(transitive_le ? n) //
          ]
        |#m #lt1m @lt_to_leb_false @(lt_to_le_to_lt … H2n)
         @le_exp [@(ltn_to_ltO ?? lep) |//]
        ]
      |@(transitive_le ? (k (2*n) p)) [@leb_true_to_le //|@le_k]
      ]
    |%2 >Hc %
    ]
  |@(transitive_le ? (∏_{p < S (sqrt (2*n)) | primeb p} (2*n)))
    [@le_pi #p #ltp #primep @(transitive_le ? (exp p (log p (2*n))))
      [@le_exp
        [@prime_to_lt_O @primeb_true_to_prime //
        |cases (true_or_false (leb 2 (k (2*n) p))) #Hc >Hc
          [>commutative_times <times_n_1 @le_k|@le_O_n]
        ]
      |@le_exp_log >(times_n_O O) in ⊢ (?%?); @lt_times //
      ]
    |@(transitive_le ? (exp (2*n) (prim(sqrt (2*n)))))
      [>exp_sigma // 
      |@le_exp
        [>(times_n_O O) in ⊢ (?%?); @lt_times // 
        |@le_prim_n3 @true_to_le_max
          [@(transitive_le ? (2*(exp 2 7)))
            [@leb_true_to_le // |@le_S @monotonic_le_times_r //]
          |@le_to_leb_true @(transitive_le ? (2*(exp 2 7)))
            [@leb_true_to_le % | @monotonic_le_times_r //]
          ]
        ]
      ]
    ]
  ]
qed.
   
theorem not_bertrand_to_le_B: 
  ∀n.exp 2 7 ≤ n → not_bertrand n →
  B (2*n) ≤ (exp 2 (2*(2 * n / 3)))*(exp (2*n) (pred(sqrt(2*n)/2))).
#n #len #notB >eq_B_Bk >eq_Bk_B1_B2 @le_times
  [@(transitive_le ? (theta ((2*n)/3)))
    [@le_B1_theta [@(transitive_le … len) @leb_true_to_le //|//]
    |@le_theta
    ]
  |@le_B2_exp //
  ]
qed.

(* 
theorem not_bertrand_to_le1: 
\forall n.18 \le n \to not_bertrand n \to
exp 2 (2*n) \le (exp 2 (2*(2 * n / 3)))*(exp (2*n) (S(sqrt(2*n)))).
*)

lemma le_times_div_m_m: ∀n,m. O < m → n/m*m ≤ n.
#n #m #posm >(div_mod n m) in ⊢ (??%); //
qed.

theorem not_bertrand_to_le1: 
  ∀n.exp 2 7 ≤ n → not_bertrand n →
  exp 2 (2*n / 3) ≤ exp (2*n) (sqrt(2*n)/2).
#n #len #notB @(le_times_to_le (exp 2 (2*(2 * n / 3))))
  [@lt_O_exp @lt_O_S
  |<exp_plus_times @(transitive_le ? (exp 2 (2*n)))
    [@(le_exp … (lt_O_S ?)) 
     cut (2*(2*n/3)+2*n/3 = 3*(2*n/3)) [//] #Heq >Heq
     >commutative_times @le_times_div_m_m @lt_O_S
    |@(transitive_le ? (2*n*B(2*n)))
      [@le_exp_B @(transitive_le …len) @leb_true_to_le //
      |<(S_pred (sqrt (2*n)/2))
        [whd in ⊢ (??(??%)); <associative_times
         <commutative_times in ⊢ (??%); @monotonic_le_times_r 
         @not_bertrand_to_le_B //
        |@(le_times_to_le_div … (lt_O_S ?))
         @(transitive_le ? (sqrt (exp 2 8)))
          [@leb_true_to_le % 
          |@monotonic_sqrt >commutative_times @le_times // 
          ]
        ]
      ]
    ]
  ]
qed.
       
theorem not_bertrand_to_le2: 
  ∀n.exp 2 7 ≤ n → not_bertrand n →
  2*n / 3 ≤ (sqrt(2*n)/2)*S(log 2 (2*n)).
#n #len #notB <(eq_log_exp 2 (2*n/3) (le_n ?))
@(transitive_le ? (log 2 ((exp (2*n) (sqrt(2*n)/2)))))
  [@le_log [@le_n|@not_bertrand_to_le1 //] |@log_exp1 @le_n]
qed.

lemma lt_div_S_div: ∀n,m. O < m → exp m 2 ≤ n → 
  n/(S m) < n/m.
#n #m #posm #len @lt_times_to_lt_div @(lt_to_le_to_lt ? (S(n/m)*m))
  [@lt_div_S //
  |<times_n_Sm >commutative_times <times_n_Sm >commutative_times @le_plus [2://] 
   @le_times_to_le_div //
  ]
qed.

lemma times_div_le: ∀a,b,c,d.O < b → O < d →
  (a/b)*(c/d) ≤ (a*c)/(b*d).
#a #b #c #d #posa #posb @le_times_to_le_div
  [>(times_n_O O) @lt_times //
  |cut (∀n,m,p,q.n*m*(p*q) = p*n*(q*m)) [//] #Heq >Heq
   @le_times //
  ]
qed.

lemma tech: ∀n. 2*(S(log 2 (2*n))) ≤ sqrt (2*n) →
  (sqrt(2*n)/2)*S(log 2 (2*n)) ≤ 2*n / 4.
#n #H
cut (4 = 2*2) [//] #H4
cut (4*(S(log 2 (2*n))) ≤ 2* sqrt(2*n)) 
  [>H4 >associative_times @monotonic_le_times_r @H] #H1
>commutative_times @(le_times_to_le_div … (lt_O_S ?))
<associative_times @(transitive_le ? (2*sqrt(2*n)*(sqrt (2*n)/2)))
  [@le_times [@H1|@le_n]
  |@(transitive_le ? ((2*sqrt(2*n)*(sqrt(2*n))/2)))
    [@le_times_div_div_times @lt_O_S
    |>associative_times >commutative_times >(div_times … (lt_O_S …)) @leq_sqrt_n
    ]
  ]
qed.

(* we need a "good" lower bound for sqrt (2*n) *)
lemma exp_to_log_r : ∀b,n,m. 1 < b → n < m → exp b n ≤ m → n ≤ log b m.
#b #n #m #lt1b #ltnm #Hexp @true_to_le_max [@ltnm |@le_to_leb_true //]
qed.

lemma square_double :∀n. 2 < n → (S n)*(S n) ≤ 2*n*n.
#n #posn normalize <times_n_Sm <plus_n_O >(plus_n_O (n+(n+n*n))) 
cut (S(n+(n+n*n)+0)=n*n+(n+(S n))) [//] #Hcut >Hcut >distributive_times_plus_r
@monotonic_le_plus_r <plus_n_Sm cut (n+n = 2*n) [//] #Hcut1 >Hcut1 
@monotonic_lt_times_l [@(ltn_to_ltO … posn) |@posn]
qed.

lemma sqrt_bound: ∀n. exp 2 8 ≤ n → 2*(S(log 2 (2*n))) ≤ sqrt (2*n).
#n #len
cut (8 ≤ log 2 n) [<(eq_log_exp 2 8) [@le_log [@le_n|@len]|@le_n]] #Hlog
cut (0<n) [@(lt_to_le_to_lt … len) @lt_O_S] #posn
>(exp_n_1 2) in ⊢ (? (? ? (? (? ? (? % ?)))) ?);
>(log_exp … (le_n ?) posn) >commutative_plus >plus_n_Sm @true_to_le_max
  [@le_S_S @monotonic_le_times_r 
   cut (2<n) [@(lt_to_le_to_lt … len) @le_S_S @le_S_S @lt_O_S] #lt2n
   elim lt2n [//] #m #lt2m #Hind 
   cut (0<m) [@(transitive_le … lt2m) @leb_true_to_le //] #posm
   @(transitive_le ? (log 2 (2*m) +2))
    [@le_plus [2://] @le_log [//] normalize <plus_n_O 
     >(plus_n_O m) in ⊢ (?%?); >plus_n_Sm @monotonic_le_plus_r //
    |>(exp_n_1 2) in ⊢ (?(?(??%)?)?);>(log_exp … (le_n ?) posm) @le_S_S @Hind
    ]
  |@le_to_leb_true >associative_times @monotonic_le_times_r 
   >commutative_plus
   lapply len @(nat_elim1 n) #m #Hind #lem
   cut (8<m) [@(transitive_le … lem) @leb_true_to_le //] #lt8m
   cut (1<m) [@(transitive_le … lt8m) @leb_true_to_le //] #lt1m
   cut (0<m) [@(transitive_le … lt1m) @leb_true_to_le //] #posm
   cases (le_to_or_lt_eq … (le_exp_log 2 m posm)) #Hclog
    [@(transitive_le … (le_exp_log 2 m posm))
     lapply (Hind … Hclog ?) [@le_exp [@lt_O_S|@exp_to_log_r [@le_n|@lt8m|@lem]]]
     -Hind #Hind @(transitive_le … Hind) >(eq_log_exp … (le_n ?)) @le_n
    |cases (le_to_or_lt_eq … lem) -lem #Hcasem
      [lapply (Hind (2^((log 2 m)-1)) ??) 
        [@le_exp [@lt_O_S] @le_plus_to_minus_r 
         @(lt_exp_to_lt 2 8) [@lt_O_S | >Hclog @Hcasem]
        |<Hclog in ⊢ (??%); @(lt_exp … (le_n…)) whd >(plus_n_O (log 2 m -1))
         >plus_n_Sm <plus_minus_m_m [@le_n | @lt_O_log @lt1m]
        |-Hind #Hind lapply (le_times … Hind (le_n 2)) 
         cut (∀a,b. a^(b+1) = a^b*a) [#a #b <plus_n_Sm <plus_n_O //] #exp_S 
         <exp_S <plus_minus_m_m [2:@lt_O_log //]
         -Hind #Hind <Hclog @(transitive_le … Hind)
         >(eq_log_exp … (le_n ?)) >(eq_log_exp … (le_n ?))
         >plus_minus_associative [2:@lt_O_log //]
         cut (2+3 ≤ 2+log 2 m) 
          [@monotonic_le_plus_r @(le_exp_to_le 2) [@le_n|>Hclog @lt_to_le @lt8m]]
         generalize in match (2+log 2 m); #a #Hle >(commutative_times 2 a)
         <associative_times @le_times [2://] <associative_times 
         >(commutative_times ? 2) lapply Hle cases a 
          [//| #a0 -Hle #Hle whd in match (S a0 -1); <(minus_n_O a0) 
           @square_double @le_S_S_to_le @lt_to_le @Hle]
        ]
      |<Hcasem >(eq_log_exp … (le_n ?)) @leb_true_to_le %
      ]
    ]
  ]
qed.

theorem bertrand_up:
   ∀n. 2^8 ≤ n → bertrand n.
#n #len @not_not_bertrand_to_bertrand % #notBn
@(absurd (2*n / 3 \le (sqrt(2*n)/2)*S(log 2 (2*n))))
  [@not_bertrand_to_le2
    [@(transitive_le ???? len) @le_exp [@lt_O_S|@le_n_Sn]|//]
  |@lt_to_not_le
   @(le_to_lt_to_lt ???? (lt_div_S_div ????))
    [@tech @sqrt_bound //
    |@(transitive_le ? (2*exp 2 8))
      [@leb_true_to_le // |@monotonic_le_times_r //]
    |@lt_O_S
    ]
  ]
qed.

(* see Bertrand256 for the complete theorem *)

