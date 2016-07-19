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

include "arithmetics/log.ma".

definition sqrt ≝
  λn.max (S n) (λx.leb (x*x) n).
  
lemma sqrt_def : ∀n.sqrt n = max (S n) (λx.leb (x*x) n).
// qed.

theorem eq_sqrt: ∀n. sqrt (n*n) = n.
#n >sqrt_def @max_spec_to_max %
  [@le_S_S //
  |@le_to_leb_true @le_n
  |#i #ltin #li @lt_to_leb_false @lt_times //
  ]
qed.

theorem le_sqrt_to_le_times_l : ∀m,n.n ≤ sqrt m → n*n ≤ m.
#m #n #len @(transitive_le ? (sqrt m * sqrt m))
  [@le_times // 
  |@leb_true_to_le @(f_max_true (λx:nat.leb (x*x) m) (S m))
   %{0} % //
  ]
qed.
 
theorem lt_sqrt_to_lt_times_l : ∀m,n.
  n < sqrt m → n*n < m.
#m #n #ltn @(transitive_le ? (sqrt m * sqrt m))
  [@(transitive_le ? (S n * S n))
    [@le_S_S // |@le_times //]
  |@le_sqrt_to_le_times_l @le_n]
qed.

theorem lt_sqrt_to_lt_times_r : ∀m,n.sqrt m < n → m < n*n.
#m #n #ltmn @not_le_to_lt % #H1
lapply (lt_max_to_false (\lambda x.leb (x*x) m) (S m) n ? ltmn)
  [@le_S_S @(transitive_le … H1) //
  |>(le_to_leb_true … H1) #H destruct (H)
  ]
qed.

lemma leq_sqrt_n : ∀n. sqrt n * sqrt n ≤ n.
#n @le_sqrt_to_le_times_l //
qed.

lemma le_sqrt_n : ∀n.sqrt n ≤ n.
#n @(transitive_le … (leq_sqrt_n n)) //
qed. 

lemma lt_sqrt_n : ∀n.1 < n → sqrt n < n.
#n #lt1n cases (le_to_or_lt_eq ? ? (le_sqrt_n n)) #Hcase
  [//
  |@False_ind @(absurd ?? (le_to_not_lt ? ? (leq_sqrt_n n)))
   >Hcase >Hcase >(times_n_1 n) in ⊢ (?%?); @monotonic_lt_times_r
    [@lt_to_le //|//]
qed.

lemma lt_sqrt: ∀n.n < (S (sqrt n))^2.
#n cases n
  [@le_n
  |#n1 cases n1
    [@leb_true_to_le // 
    |#n2 @not_le_to_lt @leb_false_to_not_le >exp_2
     @(lt_max_to_false (λx.(leb (x*x) (S(S n2)))) (S(S(S n2))))
      [@le_S_S @lt_sqrt_n @le_S_S @lt_O_S
      |@le_S_S @le_n
      ]
    ]
  ]
qed.

(* approximations *)
lemma le_sqrt_n1: ∀n. n - 2*sqrt n ≤ exp (sqrt n) 2.
#n  @le_plus_to_minus @le_S_S_to_le
cut (S ((sqrt n)\sup 2+2*sqrt n) = (exp (S(sqrt n)) 2))
  [2:#Hcut >Hcut @lt_sqrt]
>exp_2 >exp_2 generalize in match (sqrt n); #a  
normalize // 
qed.

(* falso per n=2, m=7 e n=3, m =15 
  a technical lemma used in Bertrand *)
lemma le_sqrt_nl: ∀n,m. 3 < n →
  m*(pred m)*n ≤ exp (sqrt ((exp m 2)*n)) 2.
#n #m #lt3n >(minus_n_O m) in ⊢ (? (? (? ? (? %)) ?) ?);
<eq_minus_S_pred >distributive_times_minus <times_n_1
>commutative_times >distributive_times_minus
>commutative_times
@(transitive_le ? (m*m*n -2*sqrt(m*m*n)))
  [@monotonic_le_minus_r
   @(le_exp_to_le1 ?? 2 (lt_O_S ?))
   <times_exp @(transitive_le ? ((exp 2 2)*(m*m*n)))
    [@monotonic_le_times_r >exp_2 @leq_sqrt_n
    |<exp_2 <times_exp <associative_times
     <commutative_times in ⊢ (?(?%?)?);
     >associative_times >commutative_times
     @le_times [2://] >exp_2 in ⊢ (??%); @le_times //
    ]
  |<exp_2 @le_sqrt_n1
  ]
qed.

lemma le_sqrt_log: ∀n,b. 2 < b  → log b n ≤ sqrt n.
#n #b #lt2b >sqrt_def 
@true_to_le_max
  [@le_S_S @le_log_n_n @lt_to_le //
  |@le_to_leb_true cases (le_to_or_lt_eq ? ? (le_O_n n)) #Hn
    [@(transitive_le … (le_exp_log b n Hn))
     elim (log b n)
      [@le_O_n
      |#n1 #Hind normalize in ⊢ (??%);
       cases(le_to_or_lt_eq ?? (le_O_n n1)) #H0
        [cases(le_to_or_lt_eq ? ? H0) #H1
          [@(transitive_le ? (3*(n1*n1)))
            [normalize in ⊢ (?%?); >commutative_times in ⊢ (?%?);
             whd in ⊢ (??%);
             cut (S (n1+(S n1*n1)) = n1*n1 + ((S n1) + n1))
              [normalize >commutative_plus in ⊢ (???%); normalize //] #Hcut
             >Hcut @monotonic_le_plus_r normalize in ⊢ (??%); <plus_n_O @le_plus
              [>(times_n_1 n1) in ⊢ (?%?); @monotonic_lt_times_r // |//]
            |>commutative_times @le_times //
            ]
          |<H1 normalize <plus_n_O 
           cut (4 = 2*2) [//] #H4 >H4 @lt_to_le @lt_times //
          ]
        |<H0 normalize <plus_n_O @(transitive_le … lt2b) @leb_true_to_le //
        ]
      ]
    |<Hn @le_n
    ]
  ]
qed.
  
lemma le_sqrt_log_n : ∀n,b. 2 < b → sqrt n * log b n ≤ n.
#n #b #lt2b @(transitive_le … (leq_sqrt_n ?))
@monotonic_le_times_r @le_sqrt_log //
qed.

theorem le_square_exp:∀n. 3 < n → exp n 2 ≤ exp 2 n.
#n #lt3n elim lt3n
  [@le_n
  |#m #le4m #Hind normalize <plus_n_O >commutative_times
   normalize <(commutative_times 2) normalize <associative_plus
   <plus_n_O >commutative_plus >plus_n_Sm @le_plus 
     [<exp_2 @Hind
     |elim le4m [@leb_true_to_le //]
      #m1 #lem1 #Hind1 normalize >commutative_times normalize 
      <plus_n_O <plus_n_Sm >(plus_n_O (S(m1+m1))) >plus_n_Sm >plus_n_Sm
      @le_plus [@Hind1 |>(exp_n_1 2) in ⊢ (?%?); @le_exp 
       [@lt_O_S |@(transitive_le … lem1) @leb_true_to_le //]
     ]
   ]
 ]
qed.

lemma le_log2_sqrt: ∀n. 2^4 ≤ n→ log 2 n ≤ sqrt n.
#n #le_n >sqrt_def 
@true_to_le_max
  [@le_S_S @le_log_n_n //
  |@le_to_leb_true 
   cut (0<n) [@(transitive_lt … le_n) @lt_O_S] #posn
   @(transitive_le … (le_exp_log 2 n posn))
   <exp_2 @le_square_exp @true_to_le_max
    [@(lt_to_le_to_lt … le_n) @leb_true_to_le // |@le_to_leb_true //]
  ]
qed.

lemma square_S: ∀a. (S a)^2 = a^2 + 2*a +1.
#a normalize >commutative_times normalize //
qed. 

theorem le_squareS_exp:∀n. 5 < n → exp (S n) 2 ≤ exp 2 n.
#n #lt4n elim lt4n
  [@leb_true_to_le //
  |#m #le4m #Hind >square_S whd in ⊢(??%); >commutative_times in ⊢(??%);
   normalize in ⊢(??%); <plus_n_O >associative_plus @le_plus [@Hind]
   elim le4m [@leb_true_to_le //] #a #lea #Hinda
   @(transitive_le ? (2*(2*(S a)+1)))
    [@lt_to_le whd >plus_n_Sm >(times_n_1 2) in ⊢ (?(??%)?);
     <distributive_times_plus @monotonic_le_times_r @le_plus [2://] 
     normalize // 
    |whd in ⊢ (??%); >commutative_times in ⊢(??%); @monotonic_le_times_r @Hinda
    ]
 ]
qed.
 
 
lemma lt_log2_sqrt: ∀n. 2^6 ≤ n→ log 2 n < sqrt n.
#n #le_n >sqrt_def
cut (0<n) [@(transitive_lt … le_n) @lt_O_S] #posn
@true_to_le_max
  [@le_S_S @lt_log_n_n //
  |@le_to_leb_true 
   cut (0<n) [@(transitive_lt … le_n) @lt_O_S] #posn
   @(transitive_le … (le_exp_log 2 n posn))
   <exp_2 @le_squareS_exp @true_to_le_max
    [@(lt_to_le_to_lt … le_n) @leb_true_to_le //
    |@le_to_leb_true //
    ]
  ]
qed.
 
(* monotonicity *)
theorem monotonic_sqrt: monotonic nat le sqrt.
#n #m #lenm >sqrt_def @true_to_le_max
  [@le_S_S @(transitive_le … lenm) @le_sqrt_n
  |@le_to_leb_true @(transitive_le … lenm) @leq_sqrt_n
  ]
qed.
   
   
