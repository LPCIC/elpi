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

include "arithmetics/log.ma". 
include "arithmetics/sigma_pi.ma". 

(* (prim n) counts the number of prime numbers up to n included *)
definition prim ≝ λn. ∑_{i < S n | primeb i} 1.

lemma le_prim_n: ∀n. prim n ≤ n.
#n elim n // -n #n #H
whd in ⊢ (?%?); cases (primeb (S n)) whd in ⊢ (?%?);
  [@le_S_S @H |@le_S @H]
qed.

lemma not_prime_times_2: ∀n. 1 < n → ¬prime (2*n).
#n #ltn % * #H #H1 @(absurd (2 = 2*n))
  [@H1 // %{n} //
  |@lt_to_not_eq >(times_n_1 2) in ⊢ (?%?); @monotonic_lt_times_r //
  ]
qed.

theorem eq_prim_prim_pred: ∀n. 1 < n → 
  prim (2*n) = prim (pred (2*n)).
#n #ltn 
lapply (S_pred (2*n) ?) [>(times_n_1 0) in ⊢ (?%?); @lt_times //] #H2n
lapply (not_prime_times_2 n ltn) #notp2n
whd in ⊢ (??%?); >(not_prime_to_primeb_false … notp2n) whd in ⊢ (??%?);
<H2n in ⊢ (??%?); % 
qed.

theorem le_prim_n1: ∀n. 4 ≤ n → 
  prim (S(2*n)) ≤ n.
#n #le4 elim le4 -le4
  [@le_n
  |#m #le4 cut (S (2*m) = pred (2*(S m))) [normalize //] #Heq >Heq
   <eq_prim_prim_pred [2: @le_S_S @(transitive_le … le4) //] 
   #H whd in ⊢ (?%?); cases (primeb (S (2*S m))) 
    [@le_S_S @H |@le_S @H]
  ]
qed.
    
(* usefull to kill a successor in bertrand *) 
theorem le_prim_n2: ∀n. 7 ≤ n → prim (S(2*n)) ≤ pred n.
#n #le7 elim le7 -le7
  [@le_n
  |#m #le7 cut (S (2*m) = pred (2*(S m))) [normalize //] #Heq >Heq
   <eq_prim_prim_pred [2: @le_S_S @(transitive_le … le7) //] 
   #H whd in ⊢ (?%?); 
   whd in ⊢ (??%); <(S_pred m) in ⊢ (??%); [2: @(transitive_le … le7) //]
   cases (primeb (S (2*S m))) [@le_S_S @H |@le_S @H]
  ]
qed.

lemma even_or_odd: ∀n.∃a.n=2*a ∨ n = S(2*a).
#n elim n -n 
  [%{0} %1 %
  |#n * #a * #Hn [%{a} %2 @eq_f @Hn | %{(S a)} %1 >Hn normalize //
  ]
qed.

(* la prova potrebbe essere migliorata *)
theorem le_prim_n3: ∀n. 15 ≤ n →
  prim n ≤ pred (n/2).
#n #len cases (even_or_odd (pred n)) #a * #Hpredn
  [cut (n = S (2*a)) [<Hpredn @sym_eq @S_pred @(transitive_le … len) //] #Hn
   >Hn @(transitive_le ? (pred a))
    [@le_prim_n2 @(le_times_to_le 2) [//|@le_S_S_to_le <Hn @len]
    |@monotonic_pred @le_times_to_le_div //
    ]
  |cut (n = (2*S a)) 
    [normalize normalize in Hpredn:(???%); <plus_n_Sm <Hpredn @sym_eq @S_pred
     @(transitive_le … len) //] #Hn 
   >Hn @(transitive_le ? (pred a)) 
    [>eq_prim_prim_pred 
      [2:@(lt_times_n_to_lt_r 2) <Hn @(transitive_le … len) //]
     <Hn >Hpredn @le_prim_n2 @le_S_S_to_le @(lt_times_n_to_lt_r 2) <Hn @len
    |@monotonic_pred @le_times_to_le_div //
    ]
  ]
qed. 

(* This is chebishev psi function *)
definition Psi: nat → nat ≝
  λn.∏_{p < S n | primeb p} (exp p (log p n)).
  
definition psi_def : ∀n. 
  Psi n = ∏_{p < S n | primeb p} (exp p (log p n)).
// qed.

theorem le_Psil1: ∀n.
  Psi n ≤ ∏_{p < S n | primeb p} n.
#n cases n [@le_n |#m @le_pi #i #_ #_ @le_exp_log //]
qed.

theorem le_Psil: ∀n. Psi n ≤ exp n (prim n).
#n <exp_sigma @le_Psil1
qed.

theorem lePsi_r2: ∀n.
  exp n (prim n) ≤ Psi n * Psi n.
#n elim (le_to_or_lt_eq ?? (le_O_n n)) #Hn
  [<(exp_sigma (S n) n primeb) <times_pi
   @le_pi #i #lti #primei 
   cut (1<n) 
     [@(lt_to_le_to_lt … (le_S_S_to_le … lti)) @prime_to_lt_SO 
      @primeb_true_to_prime //] #lt1n
   <exp_plus_times
   @(transitive_le ? (exp i (S(log i n))))
    [@lt_to_le @lt_exp_log @prime_to_lt_SO @primeb_true_to_prime //
    |@le_exp 
      [@prime_to_lt_O @primeb_true_to_prime //
      |>(plus_n_O (log i n)) in ⊢ (?%?); >plus_n_Sm
       @monotonic_le_plus_r @lt_O_log //
       @le_S_S_to_le //
      ]

    ]
  |<Hn @le_n
  ]
qed.

(* an equivalent formulation for psi *)
definition Psi': nat → nat ≝
λn. ∏_{p < S n | primeb p} (∏_{i < log p n} p).

lemma Psidef: ∀n. Psi' n = ∏_{p < S n | primeb p} (∏_{i < log p n} p).
// qed-.

theorem eq_Psi_Psi': ∀n.Psi n = Psi' n.
#n @same_bigop // #i #lti #primebi
@(trans_eq ? ? (exp i (∑_{x < log i n} 1)))
  [@eq_f @sym_eq @sigma_const
  |@sym_eq @exp_sigma
  ]
qed.
