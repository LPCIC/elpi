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

include "arithmetics/binomial.ma".
include "arithmetics/gcd.ma".
include "arithmetics/chebyshev/chebyshev_psi.ma". 

(* This is chebishev theta function *)

definition theta: nat → nat ≝ λn. 
  ∏_{p < S n| primeb p} p.
  
lemma theta_def: ∀n.theta n = ∏_{p < S n| primeb p} p.
// qed.

theorem lt_O_theta: ∀n. O < theta n.
#n elim n
  [@le_n
  |#n1 #Hind cases (true_or_false (primeb (S n1))) #Hc 
    [>theta_def >bigop_Strue
      [>(times_n_O O) @lt_times // | //]
    |>theta_def >bigop_Sfalse // 
    ]
  ]
qed.

theorem divides_fact_to_divides: ∀p,n. prime p → divides p n! → 
  ∃m.O < m ∧ m \le n ∧ divides p m.  
#p #n #primep elim n
  [normalize in ⊢ (%→?); #H @False_ind @(absurd (p ≤1))
    [@divides_to_le //|@lt_to_not_le @prime_to_lt_SO @primep]
  |#n1 #Hind >factS #Hdiv
   cases (divides_times_to_divides ??? primep Hdiv) #Hcase
    [%{(S n1)} %[ % [@lt_O_S |@le_n] |@Hcase]
    |cases(Hind Hcase) #a * * #posa #lea #diva
     %{a} % [% [// |@le_S //] |//]
    ]
  ]
qed.
      
theorem divides_fact_to_le: ∀p,n. prime p → divides p n! → p ≤ n.  
#p #n #primep #divp cases (divides_fact_to_divides p n primep divp)
#a * * #posa #lea #diva @(transitive_le ? a) [@divides_to_le // | //]
qed.
     
theorem prime_to_divides_M: ∀m,p. 
  prime p → S m < p → p ≤ S(2*m) → divides p (M m).      
#m #p #primep #lemp #lep >Mdef >bceq
cases (bc2 (S(2*m)) m ?)
  [#q #Hq >Hq >commutative_times >div_times
    [cases (divides_times_to_divides p (m!*(S (2*m)-m)!) q primep ?)
      [#Hdiv @False_ind
       cases (divides_times_to_divides p (m!) (S (2*m)-m)! primep ?)
        [-Hdiv #Hdiv @(absurd (p ≤ m))
          [@divides_fact_to_le //
          |@(lt_to_not_le ?? (lt_to_le ?? lemp))
          ]
        |-Hdiv #Hdiv @(absurd (p ≤S m))
          [@(divides_fact_to_le … primep)
           cut (S m = S(2*m)-m) 
            [normalize in ⊢ (???(?%?)); <plus_n_O 
             >plus_n_Sm >commutative_plus @minus_plus_m_m
            ] #HSm
           >HSm //
          |@lt_to_not_le //
          ]
        |//  
        ]
      |//
      |<Hq @divides_fact [@prime_to_lt_O // |//]
      ]
    |>(times_n_O O) in ⊢ (?%?); @lt_times //
    ]
  |normalize in ⊢ (??(?%)); <plus_n_O //
  ]
qed.
             
theorem divides_pi_p_M1: ∀m.∀i. i ≤ S(S(2*m)) → 
  ∏_{p < i | leb (S(S m)) p ∧ primeb p} p ∣ M m .
#m #i elim i
  [#_ @(quotient ?? (M m)) >commutative_times @times_n_1
  |#n #Hind #len
   cases (true_or_false (leb (S (S m)) n ∧ primeb n)) #Hc 
    [>bigop_Strue
      [@divides_to_divides_times
        [@primeb_true_to_prime @(andb_true_r ?? Hc)
        |cut (∀p.prime p → n ≤ p → ¬p∣∏_{p < n | leb (S (S m)) p∧primeb p} p)
          [2: #Hcut @(Hcut … (le_n ?)) @primeb_true_to_prime @(andb_true_r ?? Hc)]
         #p #primep elim n
          [#_ normalize @(not_to_not ? (p ≤ 1)) 
            [@divides_to_le @lt_O_S|@lt_to_not_le @prime_to_lt_SO //]
          |#n1 #Hind1 #Hn1 cases (true_or_false (leb (S (S m)) n1∧primeb n1)) #Hc1
            [>bigop_Strue 
              [% #Habs cases(divides_times_to_divides ??? primep Habs)
                [-Habs #Habs @(absurd … Hn1) @le_to_not_lt
                 @(divides_to_le … Habs) @prime_to_lt_O
                 @primeb_true_to_prime @(andb_true_r ?? Hc1)
                |-Habs #Habs @(absurd … Habs) @Hind1 @lt_to_le //
                ]
              |@Hc1
              ]
            |>bigop_Sfalse // @Hind1 @lt_to_le //
            ]
          ]
        |@prime_to_divides_M
          [@primeb_true_to_prime @(andb_true_r ?? Hc)
          |@leb_true_to_le @(andb_true_l ?? Hc)
          |@le_S_S_to_le //
          ]
        |@Hind @lt_to_le //
        ]
      |@Hc
      ]
    |>bigop_Sfalse // @Hind @lt_to_le @len
    ]
  ]
qed.

theorem divides_pi_p_M:∀m.
  ∏_{p < S(S(2*m)) | leb (S(S m)) p ∧ primeb p} p ∣ (M m).
#m  @divides_pi_p_M1 @le_n
qed.  

theorem theta_pi_p_theta: ∀m. theta (S (2*m))
= (∏_{p < S (S (2*m)) | leb (S (S m)) p∧primeb p} p)*theta (S m).
#m >theta_def >theta_def 
<(bigop_I ???? timesA)
>(bigop_sumI 0 (S(S m)) (S(S(2*m))) (λp.primeb p) … timesA (λp.p))
  [2:@le_S_S @le_S_S // |3:@le_O_n]
@eq_f2
  [>bigop_I_gen // |@(bigop_I … timesA)]
qed.

theorem div_theta_theta: ∀m. 
  theta (S(2*m))/theta (S m) = 
    ∏_{p < S(S(2*m)) | leb (S(S m)) p ∧ primeb p} p.
#m @(div_mod_spec_to_eq ????? 0 (div_mod_spec_div_mod …))
  [@lt_O_theta
  |@div_mod_spec_intro [@lt_O_theta |<plus_n_O @theta_pi_p_theta]
  ]
qed.
                     
theorem le_theta_M_theta: ∀m. 
  theta (S(2*m)) ≤ (M m)*theta (S m).  
#m >theta_pi_p_theta @le_times [2://] @divides_to_le
  [@lt_O_bc @lt_to_le @le_S_S // | @divides_pi_p_M
  ]
qed.

theorem lt_O_to_le_theta_exp_theta: ∀m. O < m→
  theta (S(2*m)) < exp 2 (2*m)*theta (S m). 
#m #posm @(le_to_lt_to_lt ? (M m*theta (S m)))
  [@le_theta_M_theta
  |@monotonic_lt_times_l [@lt_O_theta|@lt_M //]
  ]
qed.

theorem theta_pred: ∀n. 1 < n → theta (2*n) = theta (pred (2*n)).
#n #lt1n >theta_def >theta_def >bigop_Sfalse
  [>S_pred
    [//
    |>(times_n_O 2) in ⊢ (?%?); @monotonic_lt_times_r @lt_to_le //
    ]
  |@not_prime_to_primeb_false % * #lt2n #Hprime
   @(absurd (2=2*n))
    [@(Hprime … (le_n ?)) %{n} // 
    |@lt_to_not_eq >(times_n_1 2) in ⊢ (?%?); @monotonic_lt_times_r //
    ]
  ]
qed.
  
theorem le_theta: ∀m.theta m ≤ exp 2 (2*m).
#m @(nat_elim1 m) #m1 #Hind
cut (∀a. 2 *a = a+a) [//] #times2
cases (even_or_odd m1) #a * #Ha >Ha
  [lapply Ha cases a
    [#_ @le_n
    |#n cases n 
      [#_ @leb_true_to_le //
      |#n1 #Hn1 >theta_pred
        [cut (pred (2*S(S n1)) = (S (2*S n1)))
          [normalize >plus_n_Sm in ⊢ (???%); //] #Hcut >Hcut
         @(transitive_le ? (exp 2 (2*(S n1))*theta (S (S n1))))
          [@lt_to_le @lt_O_to_le_theta_exp_theta @lt_O_S
          |>times2 in ⊢ (??%);>exp_plus_times in ⊢ (??%); @le_times
            [@le_exp [@lt_O_S |@monotonic_le_times_r @le_n_Sn]
            |@Hind >Hn1 >times2 //
            ]
          ]
        |@le_S_S @lt_O_S
        ]
      ]
    ]
  |lapply Ha cases a
    [#_ @leb_true_to_le // 
    |#n #Hn @(transitive_le ? (exp 2 (2*(S n))*theta (S (S n))))
      [@lt_to_le @lt_O_to_le_theta_exp_theta @lt_O_S
      |>times2 in ⊢ (??%); <plus_n_Sm <commutative_plus >plus_n_Sm
       >exp_plus_times in ⊢ (??%); @monotonic_le_times_r
       cut (∀a. 2*(S a) = S(S(2*a))) [#a normalize <plus_n_Sm //] #timesSS
       <timesSS @Hind >Hn @le_S_S >times2 //
      ]
    ]
  ]
qed.
   
