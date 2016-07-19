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
include "arithmetics/div_and_mod.ma".
include "arithmetics/minimization.ma".

definition log ≝ λp,n.
  max n (λx.leb (exp p x) n).

lemma tech_log : ∀p,n. 1<p → 0 < n →
  log p n = max (S n) (λx.leb (exp p x) n).
#p #n #lt1p #posn whd in ⊢ (???%); 
cut (leb (exp p n) n = false) 
  [@not_le_to_leb_false @lt_to_not_le /2/
  |#Hleb >Hleb % 
  ]
qed. 
   
theorem le_exp_log: ∀p,n. O < n →
  exp p (log p n) ≤ n.
#a #n #posn @leb_true_to_le
(* whd in match (log ??); *)
@(f_max_true (λx.leb (exp a x) n)) %{0} % //
@le_to_leb_true // 
qed.

theorem log_SO: ∀n. 1 < n → log n 1 = O.
#n #lt1n @sym_eq @le_n_O_to_eq @(le_exp_to_le n) //
qed.

theorem lt_to_log_O: ∀n,m. O < m → m < n → log n m = O.
#n #m #posm #ltnm @sym_eq @le_n_O_to_eq @le_S_S_to_le @(lt_exp_to_lt n) 
  [@(le_to_lt_to_lt ? m) //
  |normalize in ⊢ (??%); <plus_n_O @(le_to_lt_to_lt ? m) //
   @le_exp_log //
  ]
qed.

theorem lt_log_n_n: ∀p, n. 1 < p → O < n → log p n < n.
#p #n #lt1p #posn
cut (log p n ≤ n)
  [whd in match (log ??); @le_max_n
  |#Hcut elim (le_to_or_lt_eq ? ? Hcut) // 
   #Hn @False_ind @(absurd … (exp p n ≤ n))
    [<Hn in ⊢ (?(??%)?); @le_exp_log //
    |@lt_to_not_le @lt_m_exp_nm //
    ]
  ]
qed.

theorem lt_O_log: ∀p, n. 1 < n → p ≤ n → O < log p n.
#p #n #lt1p #lepn whd in match (log ??);
@not_lt_to_le % #H lapply (lt_max_to_false ??? lt1p H) 
<exp_n_1 >(le_to_leb_true … lepn) #H destruct
qed.

theorem le_log_n_n: ∀p,n. 1 < p → log p n ≤ n.
#p #n #lt1p cases n [@le_n |#m @lt_to_le @lt_log_n_n //]
qed.

theorem lt_exp_log: ∀p,n. 1 < p → n < exp p (S (log p n)).
#p #n #lt1p cases n
  [normalize <plus_n_O @lt_to_le // 
  |#m @not_le_to_lt @leb_false_to_not_le
   @(lt_max_to_false ? (S(S m)) (S (log p (S m))))
    [@le_S_S @lt_log_n_n //
    |<tech_log //
    ] 
  ] 
qed. 

theorem log_times1: ∀p,n,m. 1 < p → O < n → O < m →
  log p (n*m) ≤ S(log p n+log p m). 
#p #n #m #lt1p #posn #posm  
whd in ⊢ (?(%??)?); @f_false_to_le_max
  [%{O} % 
    [>(times_n_O 0) in ⊢ (?%%); @lt_times // 
    |@le_to_leb_true normalize >(times_n_O 0) in ⊢ (?%%); @lt_times //
    ]
  |#i #Hm @lt_to_leb_false
   @(lt_to_le_to_lt ? ((exp p (S(log p n)))*(exp p (S(log p m)))))
    [@lt_times @lt_exp_log //
    |<exp_plus_times @le_exp [@lt_to_le //]
     normalize <plus_n_Sm //
    ]
  ]
qed.
  
theorem log_times: ∀p,n,m. 1 < p → 
  log p (n*m) ≤ S(log p n+log p m).
#p #n #m #lt1p cases n // -n #n cases m 
  [<times_n_O @le_O_n |-m #m @log_times1 //]
qed.

theorem log_times_l: ∀p,n,m.O < n → O < m → 1 < p → 
  log p n+log p m ≤ log p (n*m).
#p #n #m #posn #posm #lt1p whd in ⊢ (??(%??));
@true_to_le_max
  [cases posn
    [>(log_SO … lt1p) >commutative_times <times_n_1 @lt_log_n_n //
    |-n #n #posn cases posm
      [>(log_SO … lt1p) < plus_n_O <times_n_1 @lt_log_n_n //
      |#m1 #lem1 @(transitive_le ? (S n + S m1))
        [@le_S_S @le_plus // @le_S_S_to_le @lt_log_n_n // 
        |@le_S_S >commutative_plus normalize >plus_n_Sm
         @monotonic_le_plus_r >(times_n_1 n) in ⊢ (?%?); 
         @monotonic_lt_times_r // @le_S_S //
        ]
      ]
    ]
  |@le_to_leb_true >exp_plus_times @le_times @le_exp_log //
  ]
qed.

theorem log_exp: ∀p,n,m. 1 < p → O < m →
  log p ((exp p n)*m)=n+log p m.
#p #n #m #lt1p #posm whd in ⊢ (??(%??)?);
@max_spec_to_max %
  [elim n
    [<(exp_n_O p) >commutative_times <times_n_1
     @lt_log_n_n //
    |#a #Hind whd in ⊢ (?%?); 
     @(lt_to_le_to_lt ? (S((p^a) *m))) [@le_S_S @Hind]
     whd in match (exp ? (S a)); >(commutative_times ? p)
     >associative_times >(times_n_1 (p^a * m)) in ⊢ (?%?);
     >commutative_times in ⊢ (?%?); @monotonic_lt_times_l //
     >(times_n_O 0) @lt_times // @lt_O_exp @lt_to_le //
    ]
  |@le_to_leb_true >exp_plus_times
   @monotonic_le_times_r @le_exp_log //
  |#i #Hi #Hm @lt_to_leb_false
   @(lt_to_le_to_lt ? ((exp p n)*(exp p (S(log p m)))))
    [@monotonic_lt_times_r [@lt_O_exp @lt_to_le // |@lt_exp_log //]
    |<exp_plus_times @le_exp [@lt_to_le // | //]
    ]
  ]
qed.

theorem eq_log_exp: ∀p,n. 1< p →
  log p (exp p n)=n.
#p #n #lt1p  >(times_n_1 (p^n)) in ⊢ (??(??%)?); >log_exp // >log_SO //
qed.

theorem log_exp1: ∀p,n,m. 1 < p →
  log p (exp n m) ≤ m*S(log p n).
#p #n #m #lt1p elim m // -m #m #Hind
@(transitive_le ? (S (log p n+log p (n\sup m))))
  [whd in match (exp ??); >commutative_times @log_times //
  |@le_S_S @monotonic_le_plus_r //
  ]
qed.
    
theorem log_exp2: ∀p,n,m. 1 < p → 0 < n →
  m*(log p n) ≤ log p (exp n m).
#p #n #m #ltp1 #posn @le_S_S_to_le @(lt_exp_to_lt p)
  [@lt_to_le //
  |>commutative_times <exp_exp_times @(le_to_lt_to_lt ? (exp n m))
    [elim m // -m #m #Hind whd in match (exp ??); @le_times // @le_exp_log //
    |@lt_exp_log //
    ]
  ]
qed.

lemma le_log_S: ∀p,n.1 < p → 
  log p n ≤ log p (S n).
#p #n #lt1p normalize cases (leb (exp p n) (S n)) normalize //
@le_max_f_max_g #i #ltin #H @le_to_leb_true @le_S @leb_true_to_le //
qed.

theorem le_log: ∀p,n,m. 1 < p → n ≤ m → 
  log p n ≤ log p m.
#p #n #m #lt1p #lenm elim lenm // -m #m #lenm #Hind
@(transitive_le … Hind) @le_log_S // 
qed.
         
theorem log_div: ∀p,n,m. 1 < p → O < m → m ≤ n →
  log p (n/m) ≤ log p n -log p m.
#p #n #m #lt1p #posn #lemn
@le_plus_to_minus_r @(transitive_le ? (log p ((n/m)*m)))
  [@log_times_l // @le_times_to_le_div //
  |@le_log //
  ]
qed.

theorem log_n_n: ∀n. 1 < n → log n n = 1.
#n #lt1n >(exp_n_1 n) in ⊢ (??(??%)?);
>(times_n_1 (n^1)) in ⊢ (??(??%)?); >log_exp //
qed.

theorem log_i_2n: ∀n,i. 1 < n → n < i → i ≤ 2*n →
  log i (2*n) = 1.
#n #i #lt1n #ltni #lei
cut (∀a,b. a≤b → b≤a → a=b)
  [#a #b #leab #leba cases (le_to_or_lt_eq … leab)
    [#ltab @False_ind @(absurd ? ltab) @le_to_not_lt // | //]] #Hcut
@Hcut  
  [@not_lt_to_le % #H
   @(absurd ?? (lt_to_not_le (2 * n) (exp i 2) ?)) 
    [@(transitive_le ? (exp i (log i (2*n))))
      [@le_exp // @(ltn_to_ltO ? ? ltni)
      |@le_exp_log >(times_n_O O) in ⊢ (?%?); @lt_times // @lt_to_le //
      ]
    |>exp_2 @lt_times @(le_to_lt_to_lt ? n) // 
    ]
  |@(transitive_le ? (log i i))
    [<(log_n_n i) in ⊢ (?%?); // @(transitive_lt … lt1n) //  
    |@le_log // @(transitive_lt … lt1n) // 
    ]
  ]
qed.

theorem exp_n_O: ∀n. O < n → exp O n = O.
#n #posn @(lt_O_n_elim ? posn) normalize // 
qed.

