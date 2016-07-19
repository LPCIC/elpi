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

include "arithmetics/chebyshev/chebyshev_psi.ma".
include "arithmetics/chebyshev/factorization.ma".

theorem le_B_Psi: ∀n. B n ≤ Psi n.
#n >eq_Psi_Psi' @le_pi #p #ltp #primep
@le_pi #i #lti #_ >(exp_n_1 p) in ⊢ (??%); @le_exp
  [@prime_to_lt_O @primeb_true_to_prime //
  |@le_S_S_to_le @lt_mod_m_m @lt_O_S
  ]
qed.

theorem le_B_Psi4: ∀n. O < n → 2 * B (4*n) ≤ Psi (4*n).
#n #posn >eq_Psi_Psi'
cut (2 < (S (4*n)))
  [@le_S_S >(times_n_1 2) in ⊢ (?%?); @le_times //] #H2
cut (O<log 2 (4*n))
  [@lt_O_log [@le_S_S_to_le @H2 |@le_S_S_to_le @H2]] #Hlog
>Bdef >(bigop_diff ??? timesAC ? 2 ? H2) [2:%]
>Psidef >(bigop_diff ??? timesAC ? 2 ? H2) in ⊢ (??%); [2:%]
<associative_times @le_times
  [>(bigop_diff ??? timesAC ? 0 ? Hlog) [2://]
   >(bigop_diff ??? timesAC ? 0 ? Hlog) in ⊢ (??%); [2:%]
   <associative_times >timesACdef @le_times 
    [<exp_n_1 cut (4=2*2) [//] #H4 >H4 >associative_times
     >commutative_times in ⊢ (?(??(??(?(?%?)?)))?);
     >div_times [2://] >divides_to_mod_O
      [@le_n |%{n} // |@lt_O_S]
    |@le_pi #i #lti #H >(exp_n_1 2) in ⊢ (??%);
     @le_exp [@lt_O_S |@le_S_S_to_le @lt_mod_m_m @lt_O_S]
    ]
  |@le_pi #p #ltp #Hp @le_pi #i #lti #H
   >(exp_n_1 p) in ⊢ (??%); @le_exp
    [@prime_to_lt_O @primeb_true_to_prime @(andb_true_r ?? Hp)
    |@le_S_S_to_le @lt_mod_m_m @lt_O_S
    ]
  ]
qed.

let rec bool_to_nat b ≝ 
  match b with [true ⇒ 1 | false ⇒ 0].
  
theorem eq_Psi_2_n: ∀n.O < n →
Psi(2*n) =
 ∏_{p <S (2*n) | primeb p}
  (∏_{i <log p (2*n)} (exp p (bool_to_nat (leb (S n) (exp p (S i)))))) *Psi n.
#n #posn >eq_Psi_Psi' > eq_Psi_Psi' 
cut (
 ∏_{p < S n | primeb p} (∏_{i <log p n} p)
 = ∏_{p < S (2*n) | primeb p}
     (∏_{i <log p (2*n)} (p\sup(bool_to_nat (¬ (leb (S n) (exp p (S i))))))))
  [2: #Hcut >Psidef in ⊢ (???%); >Hcut
   <times_pi >Psidef @same_bigop
    [//
    |#p #lt1p #primep <times_pi @same_bigop
      [//
      |#i #lt1i #_ cases (true_or_false (leb (S n) (exp p (S i)))) #Hc >Hc
        [normalize <times_n_1 >plus_n_O //
        |normalize <plus_n_O <plus_n_O //
        ]
      ]
    ]
  |@(trans_eq ?? 
    (∏_{p < S n | primeb p} 
      (∏_{i < log p n} (p \sup(bool_to_nat (¬leb (S n) (exp p (S i))))))))
    [@same_bigop
      [//
      |#p #lt1p #primep @same_bigop
        [//
        |#i #lti#_ >lt_to_leb_false
          [normalize @plus_n_O
          |@le_S_S @(transitive_le ? (exp p (log p n)))
            [@le_exp [@prime_to_lt_O @primeb_true_to_prime //|//]
            |@le_exp_log //
            ]
          ]
        ]
      ]
    |@(trans_eq ?? 
      (∏_{p < S (2*n) | primeb p}
       (∏_{i <log p n} (p \sup(bool_to_nat (¬leb (S n) (p \sup(S i))))))))
      [@(pad_bigop_nil … timesA)
        [@le_S_S //|#i #lti #upi %2 >lt_to_log_O //]
      |@same_bigop 
        [//
        |#p #ltp #primep @(pad_bigop_nil … timesA)
          [@le_log
            [@prime_to_lt_SO @primeb_true_to_prime //|//]
          |#i #lei #iup %2 >le_to_leb_true
            [%
            |@(lt_to_le_to_lt ? (exp p (S (log p n))))
              [@lt_exp_log @prime_to_lt_SO @primeb_true_to_prime //
              |@le_exp
                [@prime_to_lt_O @primeb_true_to_prime //
                |@le_S_S //
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
qed.
               
theorem le_Psi_BPsi1: ∀n. O < n → 
  Psi(2*n) ≤ B(2*n)*Psi n.
#n #posn >(eq_Psi_2_n … posn) @le_times [2:@le_n]
>Bdef @le_pi #p #ltp #primep @le_pi #i #lti #_ @le_exp
  [@prime_to_lt_O @primeb_true_to_prime //
  |cases (true_or_false (leb (S n) (exp p (S i)))) #Hc >Hc
    [whd in ⊢ (?%?);
     cut (2*n/p\sup(S i) = 1) [2: #Hcut >Hcut @le_n]
     @(div_mod_spec_to_eq (2*n) (exp p (S i)) 
       ? (mod (2*n) (exp p (S i))) ? (minus (2*n) (exp p (S i))) )
      [@div_mod_spec_div_mod @lt_O_exp @prime_to_lt_O @primeb_true_to_prime //
      |cut (p\sup(S i)≤2*n)
        [@(transitive_le ? (exp p (log p (2*n))))
          [@le_exp [@prime_to_lt_O @primeb_true_to_prime // | //]
          |@le_exp_log >(times_n_O O) in ⊢ (?%?); @lt_times // 
          ]
        ] #Hcut
       @div_mod_spec_intro
        [@lt_plus_to_minus
          [// |normalize in ⊢ (? % ?); < plus_n_O @lt_plus @leb_true_to_le //]
        |>commutative_plus >commutative_times in ⊢ (???(??%));
         < times_n_1 @plus_minus_m_m //
        ]
      ]
    |@le_O_n
    ]
  ]
qed.

theorem le_Psi_BPsi: ∀n. Psi(2*n) \le B(2*n)*Psi n.
#n cases n [@le_n |#m @le_Psi_BPsi1 @lt_O_S]
qed.

theorem le_Psi_exp: ∀n. Psi(2*n) ≤ (exp 2 (pred (2*n)))*Psi n.
#n @(transitive_le ? (B(2*n)*Psi n))
  [@le_Psi_BPsi |@le_times [@le_B_exp |//]]
qed.

theorem lt_4_to_le_Psi_exp: ∀n. 4 < n →
  Psi(2*n) ≤ exp 2 ((2*n)-2)*Psi n.
#n #lt4n @(transitive_le ? (B(2*n)*Psi n))
  [@le_Psi_BPsi|@le_times [@(lt_4_to_le_B_exp … lt4n) |@le_n]]
qed.

(* two technical lemmas *)
lemma times_2_pred: ∀n. 2*(pred n) \le pred (2*n).
#n cases n
  [@le_n|#m @monotonic_le_plus_r @le_n_Sn]
qed.

lemma le_S_times_2: ∀n. O < n → S n ≤ 2*n.
#n #posn elim posn
  [@le_n
  |#m #posm #Hind 
   cut (2*(S m) = S(S(2*m))) [normalize <plus_n_Sm //] #Hcut >Hcut
   @le_S_S @(transitive_le … Hind) @le_n_Sn
  ]
qed.

theorem le_Psi_exp1: ∀n.
  Psi(exp 2 n) ≤ exp 2 ((2*(exp 2 n)-(S(S n)))).
#n elim n
  [@le_n
  |#n1 #Hind whd in ⊢ (?(?%)?); >commutative_times 
   @(transitive_le ??? (le_Psi_exp ?)) 
   @(transitive_le ? (2\sup(pred (2*2^n1))*2^(2*2^n1-(S(S n1)))))
    [@monotonic_le_times_r // 
    |<exp_plus_times @(le_exp … (lt_O_S ?))
     cut (S(S n1) ≤ 2*(exp 2 n1))
      [elim n1
        [@le_n
        |#n2 >commutative_times in ⊢ (%→?); #Hind1 @(transitive_le ? (2*(S(S n2))))
          [@le_S_times_2 @lt_O_S |@monotonic_le_times_r //] 
        ]
      ] #Hcut
     @le_S_S_to_le cut(∀a,b. S a + b = S (a+b)) [//] #Hplus <Hplus >S_pred
      [>eq_minus_S_pred in ⊢ (??%); >S_pred
        [>plus_minus_associative
          [@monotonic_le_minus_l
           cut (∀a. 2*a = a + a) [//] #times2 <times2 
           @monotonic_le_times_r >commutative_times @le_n
          |@Hcut
          ]
        |@lt_plus_to_minus_r whd in ⊢ (?%?);
         @(lt_to_le_to_lt ? (2*(S(S n1))))
          [>(times_n_1 (S(S n1))) in ⊢ (?%?); >commutative_times
           @monotonic_lt_times_l [@lt_O_S |@le_n]
          |@monotonic_le_times_r whd in ⊢ (??%); //
          ]
        ]
      |whd >(times_n_1 1) in ⊢ (?%?); @le_times
        [@le_n_Sn |@lt_O_exp @lt_O_S]
      ]
    ]
  ]
qed.

theorem monotonic_Psi: monotonic nat le Psi.
#n #m #lenm elim lenm
  [@le_n
  |#n1 #len #Hind @(transitive_le … Hind)
   cut (∏_{p < S n1 | primeb p}(p^(log p n1))
          ≤∏_{p < S n1 | primeb p}(p^(log p (S n1))))
    [@le_pi #p #ltp #primep @le_exp
      [@prime_to_lt_O @primeb_true_to_prime //
      |@le_log [@prime_to_lt_SO @primeb_true_to_prime // | //]
      ]
    ] #Hcut
   >psi_def in ⊢ (??%); cases (true_or_false (primeb (S n1))) #Hc
    [>bigop_Strue in ⊢ (??%); [2://]
     >(times_n_1 (Psi n1)) >commutative_times @le_times
      [@lt_O_exp @lt_O_S |@Hcut]
    |>bigop_Sfalse in ⊢ (??%); // 
    ]
  ]
qed.

(* example *)
example Psi_1: Psi 1 = 1. // qed.

example Psi_2: Psi 2 = 2. // qed.

example Psi_3: Psi 3 = 6. // qed.

example Psi_4: Psi 4 = 12. // qed.

theorem le_Psi_exp4: ∀n. 1 < n →
  Psi(n) ≤ (pred n)*exp 2 ((2 * n) -3).
#n @(nat_elim1 n)
#m #Hind cases (even_or_odd m)
#a * #Hm >Hm #Hlt
  [cut (0<a) 
    [cases a in Hlt; 
      [whd in ⊢ (??%→?); #lt10 @False_ind @(absurd ? lt10 (not_le_Sn_O 1))
    |#b #_ //]
    ] #Hcut 
   cases (le_to_or_lt_eq … Hcut) #Ha
    [@(transitive_le ? (exp 2 (pred(2*a))*Psi a))
      [@le_Psi_exp
      |@(transitive_le ? (2\sup(pred(2*a))*((pred a)*2\sup((2*a)-3))))
        [@monotonic_le_times_r @(Hind ?? Ha)
         >Hm >(times_n_1 a) in ⊢ (?%?); >commutative_times
         @monotonic_lt_times_l [@lt_to_le // |@le_n]
        |<Hm <associative_times >commutative_times in ⊢ (?(?%?)?);
         >associative_times; @le_times
          [>Hm cases a[@le_n|#b normalize @le_plus_n_r]
          |<exp_plus_times @le_exp
            [@lt_O_S
            |@(transitive_le ? (m+(m-3)))
              [@monotonic_le_plus_l // 
              |normalize <plus_n_O >plus_minus_associative
                [@le_n
                |>Hm @(transitive_le ? (2*2) ? (le_n_Sn 3))
                 @monotonic_le_times_r //
                ]
              ]
            ]
          ]
        ]
      ]
    |<Ha normalize @le_n
    ]
  |cases (le_to_or_lt_eq O a (le_O_n ?)) #Ha
    [@(transitive_le ? (Psi (2*(S a))))
      [@monotonic_Psi >Hm normalize <plus_n_Sm @le_n_Sn
      |@(transitive_le … (le_Psi_exp ?) ) 
       @(transitive_le ? ((2\sup(pred (2*S a)))*(a*(exp 2 ((2*(S a))-3)))))
        [@monotonic_le_times_r @Hind
          [>Hm @le_S_S >(times_n_1 a) in ⊢ (?%?); >commutative_times
           @monotonic_lt_times_l //
          |@le_S_S //
          ]
        |cut (pred (S (2*a)) = 2*a) [//] #Spred >Spred
         cut (pred (2*(S a)) = S (2 * a)) [normalize //] #Spred1 >Spred1
         cut (2*(S a) = S(S(2*a))) [normalize <plus_n_Sm //] #times2 
         cut (exp 2 (2*S a -3) = 2*(exp 2 (S(2*a) -3))) 
          [>(commutative_times 2) in ⊢ (???%); >times2 >minus_Sn_m [%]
           @le_S_S >(times_n_1 2) in ⊢ (?%?); @monotonic_le_times_r @Ha
          ] #Hcut >Hcut
         <associative_times in ⊢ (? (? ? %) ?); <associative_times
         >commutative_times in ⊢ (? (? % ?) ?);
         >commutative_times in ⊢ (? (? (? % ?) ?) ?);
         >associative_times @monotonic_le_times_r
         <exp_plus_times @(le_exp … (lt_O_S ?))
         >plus_minus_associative
          [normalize >(plus_n_O (a+(a+0))) in ⊢ (?(?(??%)?)?); @le_n
          |@le_S_S >(times_n_1 2) in ⊢ (?%?); @monotonic_le_times_r @Ha
          ]
        ]
      ]
    |@False_ind <Ha in Hlt; normalize #Hfalse @(absurd ? Hfalse) //
    ]
  ]
qed.

theorem le_n_8_to_le_Psi_exp: ∀n. n ≤ 8 → 
  Psi(n) ≤ exp 2 ((2 * n) -3).
#n cases n
  [#_ @le_n
  |#n1 cases n1
    [#_ @le_n
    |#n2 cases n2
      [#_ @le_n
      |#n3 cases n3
        [#_ @leb_true_to_le //
        |#n4 cases n4
          [#_ @leb_true_to_le //
          |#n5 cases n5
            [#_ @leb_true_to_le //
            |#n6 cases n6
              [#_ @leb_true_to_le //
              |#n7 cases n7
                [#_ @leb_true_to_le //
                |#n8 cases n8
                  [#_ @leb_true_to_le //
                  |#n9 #H @False_ind @(absurd ?? (lt_to_not_le ?? H))
                   @leb_true_to_le //
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
qed.
           
theorem le_Psi_exp5: ∀n. Psi(n) ≤ exp 2 ((2 * n) -3).
#n @(nat_elim1 n) #m #Hind
cases (decidable_le 9 m)
  [#lem cases (even_or_odd m) #a * #Hm
    [>Hm in ⊢ (?%?); @(transitive_le … (le_Psi_exp ?))
     @(transitive_le ? (2\sup(pred(2*a))*(2\sup((2*a)-3))))
      [@monotonic_le_times_r @Hind >Hm >(times_n_1 a) in ⊢ (?%?); 
       >commutative_times @(monotonic_lt_times_l  … (le_n ?))
       @(transitive_lt ? 3)
        [@lt_O_S |@(le_times_to_le 2) [@lt_O_S |<Hm @lt_to_le @lem]]
      |<Hm <exp_plus_times @(le_exp … (lt_O_S ?))
       whd in match (times 2 m); >commutative_times <times_n_1
       <plus_minus_associative
        [@monotonic_le_plus_l @le_pred_n
        |@(transitive_le … lem) @leb_true_to_le //
        ]
      ]
    |@(transitive_le ? (Psi (2*(S a))))
      [@monotonic_Psi >Hm normalize <plus_n_Sm @le_n_Sn
      |@(transitive_le ? ((exp 2 ((2*(S a))-2))*Psi (S a)))
        [@lt_4_to_le_Psi_exp @le_S_S
         @(le_times_to_le 2)[@le_n_Sn|@le_S_S_to_le <Hm @lem]
        |@(transitive_le ? ((2\sup((2*S a)-2))*(exp 2 ((2*(S a))-3))))
          [@monotonic_le_times_r @Hind >Hm @le_S_S
           >(times_n_1 a) in ⊢ (?%?); 
           >commutative_times @(monotonic_lt_times_l  … (le_n ?))
           @(transitive_lt ? 3)
            [@lt_O_S |@(le_times_to_le 2) [@lt_O_S |@le_S_S_to_le <Hm @lem]]
          |cut (∀a. 2*(S a) = S(S(2*a))) [normalize #a <plus_n_Sm //] #times2
           >times2 <Hm <exp_plus_times @(le_exp … (lt_O_S ?))
           cases m
            [@le_n
            |#n1 cases n1
              [@le_n
              |#n2 normalize <minus_n_O <plus_n_O <plus_n_Sm
               normalize <minus_n_O <plus_n_Sm @le_n
              ]
            ]
          ]
        ]
      ]
    ]
  |#H @le_n_8_to_le_Psi_exp @le_S_S_to_le @not_le_to_lt //
  ]
qed.       

theorem le_exp_Psil:∀n. O < n → exp 2 n ≤ Psi (2 * n).
#n #posn @(transitive_le ? ((exp 2 (2*n))/(2*n)))
  [@le_times_to_le_div
    [>(times_n_O O) in ⊢ (?%?); @lt_times [@lt_O_S|//]
    |normalize in ⊢ (??(??%)); < plus_n_O >exp_plus_times
     @le_times [2://] elim posn [//]
     #m #le1m #Hind whd in ⊢ (??%); >commutative_times in ⊢ (??%);
     @monotonic_le_times_r @(transitive_le … Hind) 
     >(times_n_1 m) in ⊢ (?%?); >commutative_times 
     @(monotonic_lt_times_l  … (le_n ?)) @le1m
    ]
  |@le_times_to_le_div2
    [>(times_n_O O) in ⊢ (?%?); @lt_times [@lt_O_S|//]
    |@(transitive_le ? ((B (2*n)*(2*n))))
      [<commutative_times in ⊢ (??%); @le_exp_B //
      |@le_times [@le_B_Psi|@le_n]
      ]
    ]
  ]
qed.

theorem le_exp_Psi2:∀n. 1 < n → exp 2 (n / 2) \le Psi n.
#n #lt1n @(transitive_le ? (Psi(n/2*2)))
  [>commutative_times @le_exp_Psil
   cases (le_to_or_lt_eq ? ? (le_O_n (n/2))) [//]
   #Heq @False_ind @(absurd ?? (lt_to_not_le ?? lt1n))
   >(div_mod n 2) <Heq whd in ⊢ (?%?);
   @le_S_S_to_le @(lt_mod_m_m n 2) @lt_O_S
  |@monotonic_Psi >(div_mod n 2) in ⊢ (??%); @le_plus_n_r
  ]
qed.

theorem eq_sigma_pi_SO_n: ∀n.∑_{i < n} 1 = n.
#n elim n //
qed.

theorem lePsi_prim: ∀n.
  exp n (prim n) \le Psi n * ∏_{p < S n | primeb p} p.
#n <(exp_sigma (S n) n primeb) <times_pi @le_pi
#p #ltp #primep @lt_to_le @lt_exp_log
@prime_to_lt_SO @primeb_true_to_prime //
qed.

theorem le_prim_log : ∀n,b. 1 < b →
  log b (Psi n) ≤ prim n * (S (log b n)).
#n #b #lt1b @(transitive_le … (log_exp1 …)) [@le_log // | //]
qed.

(*********************** the inequalities ***********************)
lemma exp_Sn: ∀b,n. exp b (S n) = b * (exp b n).
normalize // 
qed.

theorem le_exp_priml: ∀n. O < n →
  exp 2 (2*n) ≤ exp (2*n) (S(prim (2*n))).
#n #posn @(transitive_le ? (((2*n*(B (2*n))))))
  [@le_exp_B // 
  |>exp_Sn @monotonic_le_times_r @(transitive_le ? (Psi (2*n)))
    [@le_B_Psi |@le_Psil]
  ]
qed.

theorem le_exp_prim4l: ∀n. O < n →
  exp 2 (S(4*n)) ≤ exp (4*n) (S(prim (4*n))).
#n #posn @(transitive_le ? (2*(4*n*(B (4*n)))))
  [>exp_Sn @monotonic_le_times_r
   cut (4*n = 2*(2*n)) [<associative_times //] #Hcut
   >Hcut @le_exp_B @lt_to_le whd >(times_n_1 2) in ⊢ (?%?);
   @monotonic_le_times_r //
  |>exp_Sn <associative_times >commutative_times in ⊢ (?(?%?)?);
   >associative_times @monotonic_le_times_r @(transitive_le ? (Psi (4*n)))
    [@le_B_Psi4 // |@le_Psil]
  ]
qed.

theorem le_priml: ∀n. O < n →
  2*n ≤ (S (log 2 (2*n)))*S(prim (2*n)).
#n #posn <(eq_log_exp 2 (2*n) ?) in ⊢ (?%?);
  [@(transitive_le ? ((log 2) (exp (2*n) (S(prim (2*n))))))
    [@le_log [@le_n |@le_exp_priml //]
    |>commutative_times in ⊢ (??%); @log_exp1 @le_n
    ]
  |@le_n
  ]
qed.

theorem le_exp_primr: ∀n.
  exp n (prim n) ≤ exp 2 (2*(2*n-3)).
#n @(transitive_le ? (exp (Psi n) 2))
  [>exp_Sn >exp_Sn whd in match (exp ? 0); <times_n_1 @lePsi_r2
  |>commutative_times <exp_exp_times @le_exp1 [@lt_O_S |@le_Psi_exp5]
  ]
qed.

(* bounds *)
theorem le_primr: ∀n. 1 < n → prim n \le 2*(2*n-3)/log 2 n.
#n #lt1n @le_times_to_le_div
  [@lt_O_log // 
  |@(transitive_le ? (log 2 (exp n (prim n))))
    [>commutative_times @log_exp2
      [@le_n |@lt_to_le //]
    |<(eq_log_exp 2 (2*(2*n-3))) in ⊢ (??%);
      [@le_log [@le_n |@le_exp_primr]
      |@le_n
      ]
    ]
  ]
qed.
     
theorem le_priml1: ∀n. O < n →
  2*n/((log 2 n)+2) - 1 ≤ prim (2*n).
#n #posn @le_plus_to_minus @le_times_to_le_div2
  [>commutative_plus @lt_O_S
  |>commutative_times in ⊢ (??%); <plus_n_Sm <plus_n_Sm in ⊢ (??(??%));
   <plus_n_O <commutative_plus <log_exp
    [@le_priml // | //| @le_n]
  ]
qed.




