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

include "arithmetics/exp.ma".
include "arithmetics/gcd.ma".
include "arithmetics/permutation.ma".
include "arithmetics/congruence.ma".
include "arithmetics/sigma_pi.ma".

theorem permut_S_mod: ∀n:nat. permut (S_mod (S n)) n.
#n %
  [#i #lein @le_S_S_to_le @lt_mod_m_m //
  |#i #j #lein #lejn #Heq @injective_S
   <(lt_to_eq_mod i (S n)) [2: @le_S_S @lein]
   <(lt_to_eq_mod j (S n)) [2: @le_S_S @lejn]
   cases (le_to_or_lt_eq … lein) #Hi
   cases (le_to_or_lt_eq … lejn) #Hj
    [(* i < n, j< n *)
     <mod_S 
      [<mod_S 
        [@Heq |@le_S_S >lt_to_eq_mod // @le_S // |//]
      |@le_S_S >lt_to_eq_mod // @le_S // 
      |//
      ]
    |(* i < n, j=n *)
     @False_ind @(absurd ?? (not_eq_O_S (i \mod (S n))))
     @sym_eq <(mod_n_n (S n)) [2://]
     <Hj in ⊢ (???(?%?)); <mod_S
      [@Heq |>lt_to_eq_mod [@le_S_S @Hi |@le_S_S @lt_to_le @Hi]|//]
    |(* i = n, j < n *)
     @False_ind @(absurd ?? (not_eq_O_S (j \mod (S n))))
     <(mod_n_n (S n)) [2://]
     <Hi in ⊢ (??(?%?)?); <mod_S
      [@Heq |>lt_to_eq_mod [@le_S_S @Hj |@le_S_S @lt_to_le @Hj]|//]
    |(* i = n, j= n*) 
     >Hi >Hj %
    ]
  ]
qed.

theorem prime_to_not_divides_fact: ∀p.prime p → ∀n.n < p → p ∤ n!.
#p #primep #n elim n 
  [normalize #_ % #divp @(absurd (p ≤1)) 
    [@divides_to_le // |@lt_to_not_le @prime_to_lt_SO //]
  |#n1 #Hind #ltn1 whd in match (fact ?); % #Hdiv
   cases (divides_times_to_divides … Hdiv)
    [-Hdiv #Hdiv @(absurd … Hdiv) @Hind @lt_to_le //
    |-Hdiv #Hdiv @(absurd … (p ≤ S n1))
      [@divides_to_le // |@lt_to_not_le //]
    |@primep
    ]
  ]
qed.

theorem permut_mod: ∀p,a:nat. prime p →
  p ∤ a → permut (λn.(mod (a*n) p)) (pred p).
#p #a #primep #ndiv % 
  [#i #lei @le_S_S_to_le @(transitive_le ? p)
    [@lt_mod_m_m @prime_to_lt_O //
    |>S_pred [//| @prime_to_lt_O //]
    ]
  |#i #j #lei #lej #H cases (decidable_lt i j)
    [(* i < j *) #ltij 
     @False_ind @(absurd (j-i < p))
      [<(S_pred p) [2:@prime_to_lt_O //] 
       @le_S_S @le_plus_to_minus @(transitive_le … lej) //
      |@le_to_not_lt @divides_to_le [@lt_plus_to_minus_r //] 
       cut (p ∣ a ∨ p ∣ (j-i))
        [2:* [#Hdiv @False_ind /2/ | //]]
       @divides_times_to_divides // >distributive_times_minus
       @eq_mod_to_divides // @prime_to_lt_O //
      ]
    |#Hij cases (le_to_or_lt_eq … (not_lt_to_le … Hij)) -Hij #Hij
      [(* j < i *)
       @False_ind @(absurd (i-j < p))
        [<(S_pred p) [2:@prime_to_lt_O //] 
         @le_S_S @le_plus_to_minus @(transitive_le … lei) //
        |@le_to_not_lt @divides_to_le [@lt_plus_to_minus_r //] 
         cut (p ∣ a ∨ p ∣ (i-j))
          [2:* [#Hdiv @False_ind /2/ | //]]
         @divides_times_to_divides // >distributive_times_minus
         @eq_mod_to_divides // @prime_to_lt_O //
        ]
      |(* i = j *) //
      ]
    ]
  ]
qed.

theorem eq_fact_pi_p:∀n.
  fact n = ∏_{i ∈ [1,S n[ } i.
#n elim n // #n1 #Hind whd in ⊢ (??%?); >commutative_times >bigop_Strue 
  [cut (S n1 -1 = n1) [normalize //] #Hcut  
   <plus_n_Sm <plus_n_O @eq_f <Hcut in ⊢ (???%); // | % ]
qed.

theorem congruent_pi: ∀f,n,p.O < p →
  congruent (∏_{i < n}(f i)) (∏_{i < n} (mod (f i) p)) p.
#f #n elim n // #n1 #Hind #p #posp >bigop_Strue //
@congruent_times // [@congruent_n_mod_n // |@Hind //]
qed. 

theorem congruent_exp_pred_SO: ∀p,a:nat. prime p → ¬ divides p a →
congruent (exp a (pred p)) (S O) p.
#p #a #primep #ndiv 
cut (0 < a) 
  [lapply ndiv cases a // * #div0 @False_ind @div0 @(quotient ? 0 0) //] #posa 
cut (O < p) [@prime_to_lt_O //] #posp
cut (O < pred p) [@le_S_S_to_le >S_pred [@prime_to_lt_SO //| @posp] ] #pospred
@(divides_to_congruent … posp) 
  [@lt_O_exp //
  |cut (divides p (exp a (pred p)-1) ∨ divides p (pred p)!)
    [@divides_times_to_divides // >commutative_times
     >distributive_times_minus <times_n_1
     >eq_fact_pi_p >commutative_times 
     cut (pred p = S (pred p) -1) [//] #Hpred >Hpred in match (exp a ?);
     >exp_pi_bc @congruent_to_divides //
     @(transitive_congruent p ? (∏_{i ∈ [1,S(pred p)[ }(a*i \mod p)))
      [@(congruent_pi (λm.a*(m +1))) //
      |cut (∏_{i ∈ [1,S(pred p)[ } i =  ∏_{i ∈ [1,S(pred p)[ } (a*i\mod p)) 
        [2: #Heq <Heq @congruent_n_n]
       >(bigop_I_gen 1 (S (pred p)) … 1 timesA) //
       >(bigop_I_gen 1 (S (pred p)) … 1 timesA) //
       @sym_eq @(bigop_iso … timesAC) 
       lapply (permut_mod … primep ndiv) #Hpermut
       %{(λi.a*i \mod p)} %{(invert_permut (pred p) (λi.a*i \mod p))} %
        [%
          [#i #lti #_ % 
          |#i #lti #posi % 
            [% 
              [>(S_pred … posp) @lt_mod_m_m //
              |>le_to_leb_true // 
               cases (le_to_or_lt_eq … (le_O_n (a*i \mod p))) [//]
               #H @False_ind @(absurd ? (mod_O_to_divides …(sym_eq  … H))) //
               @(not_to_not … ndiv) #Hdiv cases(divides_times_to_divides … Hdiv)
               // #divpi @False_ind @(absurd ? lti) @le_to_not_lt 
               >(S_pred … posp) @divides_to_le // @leb_true_to_le 
               @(andb_true_l … posi)
              ]
            |@invert_permut_f [@le_S_S_to_le //|cases Hpermut // ]
            ]
          ]
        |lapply (permut_invert_permut … Hpermut) *
         #le_invert_permut #inj_inv_permut
         #i #lti #posi % 
          [% 
            [@le_S_S @le_invert_permut @le_S_S_to_le // 
            |>le_to_leb_true //
             cases (le_to_or_lt_eq … 
               (le_O_n (invert_permut (pred p) (λi.a*i \mod p) i))) [//]
             #H @False_ind
             cut (a*0 \mod p = 0) [<times_n_O //] #H0 
             cut (a*0 \mod p = a*(invert_permut (pred p) (λi.a*i \mod p) i) \mod p)
               [@(eq_f ?? (λi.a*i \mod p)) //] 
             >H0 >(f_invert_permut (λi.a*i \mod p) … Hpermut) [2:@le_S_S_to_le //]
             #eq0i <eq0i in posi; normalize #H destruct (H)
            ]
          |@f_invert_permut [@le_S_S_to_le //| @Hpermut ]
          ]
        ]
      ]
    |* // #Hdiv @False_ind
     @(absurd ? Hdiv (prime_to_not_divides_fact p primep (pred p) ?))
     @le_S_S_to_le >S_pred //
    ]
  ]
qed.

