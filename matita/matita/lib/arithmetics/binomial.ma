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

include "arithmetics/primes.ma".
include "arithmetics/sigma_pi.ma".

(* binomial coefficient *)
definition bc ≝ λn,k. n!/(k!*(n-k)!).

lemma bceq :∀n,k. bc n k = n!/(k!*(n-k)!).
// qed.

theorem bc_n_n: ∀n. bc n n = 1.
#n >bceq <minus_n_n <times_n_1 @div_n_n //
qed.

theorem bc_n_O: ∀n. bc n O = 1.
#n >bceq <minus_n_O /2 by injective_plus_r/
qed.

theorem fact_minus: ∀n,k. k < n → 
  (n - S k)!*(n-k) = (n - k)!.
#n #k (cases n)
  [#ltO @False_ind /2/
  |#l #ltl >(minus_Sn_m k) [// |@le_S_S_to_le //]
  ]
qed.

theorem bc2 : ∀n.
∀k. k ≤n → k!*(n-k)! ∣ n!.
#n (elim n) 
  [#k #lek0 <(le_n_O_to_eq ? lek0) //
  |#m #Hind #k (cases k) normalize //
     #c #lec cases (le_to_or_lt_eq … (le_S_S_to_le …lec))
    [#ltcm 
     cut (m-(m-(S c)) = S c) [@plus_to_minus @plus_minus_m_m //] #eqSc     
     lapply (Hind c (le_S_S_to_le … lec)) #Hc
     lapply (Hind (m - (S c)) ?) [@le_plus_to_minus //] >eqSc #Hmc
     >(plus_minus_m_m m c) in ⊢ (??(??(?%))); [|@le_S_S_to_le //]
     >commutative_plus >(distributive_times_plus ? (S c))
     @divides_plus
      [>associative_times >(commutative_times (S c))
       <associative_times @divides_times //
      |<(fact_minus …ltcm) in ⊢ (?(??%)?);
       <associative_times @divides_times //
       >commutative_times @Hmc
      ]
    |#eqcm >eqcm <minus_n_n <times_n_1 // 
    ]
  ]
qed.
           
theorem bc1: ∀n.∀k. k < n → 
  bc (S n) (S k) = (bc n k) + (bc n (S k)).
#n #k #ltkn > bceq >(bceq n) >(bceq n (S k))
>(div_times_times ?? (S k)) in ⊢ (???(?%?));
  [|>(times_n_O 0) @lt_times // | //]
>associative_times in ⊢ (???(?(??%)?));
>commutative_times in ⊢ (???(?(??(??%))?));
<associative_times in ⊢ (???(?(??%)?));
>(div_times_times ?? (n - k)) in ⊢ (???(??%)) ; 
  [|>(times_n_O 0) @lt_times // 
   |@(le_plus_to_le_r k ??) <plus_minus_m_m /2 by lt_to_le/]
>associative_times in ⊢ (???(??(??%)));
>fact_minus // <plus_div 
  [<distributive_times_plus
   >commutative_plus in ⊢ (???%); <plus_n_Sm <plus_minus_m_m [|/2 by lt_to_le/] @refl
  |<fact_minus // <associative_times @divides_times // @(bc2 n (S k)) //
  |>associative_times >(commutative_times (S k))
   <associative_times @divides_times // @bc2 /2 by lt_to_le/
  |>(times_n_O 0) @lt_times [@(le_1_fact (S k)) | //]
  ]
qed.

theorem lt_O_bc: ∀n,m. m ≤ n → O < bc n m.
#n (elim n) 
  [#m #lemO @(le_n_O_elim ? lemO) //
  |-n #n #Hind #m (cases m) //
   #m #lemn cases(le_to_or_lt_eq … (le_S_S_to_le …lemn)) //
   #ltmn >bc1 // >(plus_O_n 0) @lt_plus @Hind /2/
  ]
qed. 

theorem binomial_law:∀a,b,n.
  (a+b)^n = ∑_{k < S n}((bc n k)*(a^(n-k))*(b^k)).
#a #b #n (elim n) //
-n #n #Hind normalize in ⊢ (??%?); >commutative_times
>bigop_Strue // >Hind >distributive_times_plus_r
<(minus_n_n (S n)) (* <commutative_times <(commutative_times b) *)
(* da capire *)
>(bigop_distr ??? 0 (mk_Dop ℕ O plusAC times (λn0:ℕ.sym_eq ℕ O (n0*O) (times_n_O n0))
    distributive_times_plus) ? a) 
>(bigop_distr ???? (mk_Dop ℕ O plusAC times (λn0:ℕ.sym_eq ℕ O (n0*O) (times_n_O n0))
    distributive_times_plus) ? b)
>bigop_Strue in ⊢ (??(??%)?); // <associative_plus 
<commutative_plus in ⊢ (??(? % ?) ?); >associative_plus @eq_f2
  [<minus_n_n >bc_n_n >bc_n_n normalize //
  |>(bigop_0 ??? plusA)  >associative_plus >commutative_plus in ⊢ (??(??%)?);
   <associative_plus >(bigop_0 n ?? plusA) @eq_f2 
    [cut (∀a,b. plus a b = plusAC a b) [//] #Hplus >Hplus 
     >(bigop_op n ??? plusAC) @same_bigop //
     #i #ltin #_ <associative_times >(commutative_times b)
     >(associative_times ?? b) <Hplus <(distributive_times_plus_r (b^(S i)))
     @eq_f2 // <associative_times >(commutative_times a) 
     >associative_times cut(∀n.a*a^n = a^(S n)) [#n @commutative_times] #H
     >H <minus_Sn_m // <(distributive_times_plus_r (a^(n-i)))
     @eq_f2 // @sym_eq >commutative_plus @bc1 //
    |>bc_n_O >bc_n_O normalize // 
    ]
  ]
qed.
     
theorem exp_S_sigma_p:∀a,n.
  (S a)^n = ∑_{k < S n}((bc n k)*a^(n-k)).
#a #n cut (S a = a + 1) // #H >H
>binomial_law @same_bigop //
qed.

(************ mid value *************)
lemma eqb_sym: ∀a,b. eqb a b = eqb b a.
#a #b cases (true_or_false (eqb a b)) #Hab
  [>(eqb_true_to_eq … Hab) // 
  |>Hab @sym_eq @not_eq_to_eqb_false 
   @(not_to_not … (eqb_false_to_not_eq … Hab)) //
  ] 
qed-.

definition M ≝ λm.bc (S(2*m)) m.

lemma Mdef : ∀m. M m = bc (S(2*m)) m. 
// qed.

theorem lt_M: ∀m. O < m → M m < exp 2 (2*m).
#m #posm  @(lt_times_n_to_lt_l 2)
cut (∀a,b. a^(S b) = a^b*a) [//] #expS <expS  
cut (2 = 1+1) [//] #H2 >H2 in ⊢ (??(?%?));
>binomial_law 
@(le_to_lt_to_lt ? 
  (∑_{k < S (S (2*m)) | orb (eqb k m) (eqb k (S m))}
         (bc (S (2*m)) k*1^(S (2*m)-k)*1^k)))
  [>(bigop_diff ??? plusAC … m)
    [>(bigop_diff ??? plusAC … (S m))
      [<(pad_bigop1 … (S(S(2*m))) 0)
        [cut (∀a,b. plus a b = plusAC a b) [//] #Hplus <Hplus <Hplus
         whd in ⊢ (? ? (? ? (? ? %)));
         cut (∀a. 2*a = a + a) [//] #H2a >commutative_times >H2a
         <exp_1_n <exp_1_n <exp_1_n <exp_1_n
         <times_n_1 <times_n_1 <times_n_1 <times_n_1 
         @le_plus
          [@le_n
          |>Mdef <plus_n_O >bceq >bceq 
           cut (∀a,b.S a - (S b) = a -b) [//] #Hminus >Hminus 
           normalize in ⊢ (??(??(??(?(?%?))))); <plus_n_O <minus_plus_m_m
           <commutative_times in ⊢ (??(??%)); 
           cut (S (2*m)-m = S m) 
            [>H2a >plus_n_Sm >commutative_plus <minus_plus_m_m //] 
           #Hcut >Hcut //
          ]
        |#i #_ #_ >(eqb_sym i m) >(eqb_sym i (S m))
         cases (eqb m i) cases (eqb (S m) i) //
        |@le_O_n
        ]
      |>(eqb_sym (S m) m) >(eq_to_eqb_true ? ? (refl ? (S m)))
       >(not_eq_to_eqb_false m (S m)) 
        [// |@(not_to_not … (not_eq_n_Sn m)) //]
      |@le_S_S @le_S_S // 
      ]
    |>(eq_to_eqb_true ?? (refl ? m)) //
    |@le_S @le_S_S //
    ]
  |@lt_sigma_p
    [//
    |#i #lti #Hi @le_n
    |%{0} %
      [@lt_O_S
      |%2 % 
        [% // >(not_eq_to_eqb_false 0 (S m)) //
         >(not_eq_to_eqb_false 0 m) // @lt_to_not_eq //
        |>bc_n_O <exp_1_n <exp_1_n @le_n
        ]
      ]
    ]
  ]
qed.
      
