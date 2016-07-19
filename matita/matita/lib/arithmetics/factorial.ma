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

let rec fact n ≝
  match n with 
  [ O ⇒ 1
  | S m ⇒ fact m * S m].
  
interpretation "factorial" 'fact n = (fact n).

lemma factS: ∀n. (S n)! = (S n)*n!.
#n >commutative_times // qed.

theorem le_1_fact : ∀n. 1 ≤ n!.
#n (elim n) normalize /2 by lt_minus_to_plus/ 
qed.

theorem le_2_fact : ∀n. 1 < n → 2 ≤ n!.
#n (cases n)
  [#abs @False_ind /2/
  |#m normalize #le2 @(le_times 1 ? 2) //
  ]
qed.

theorem le_n_fact_n: ∀n. n ≤ n!.
#n (elim n) normalize //
#n #Hind @(transitive_le ? (1*(S n))) // @le_times //
qed.

theorem lt_n_fact_n: ∀n. 2 < n → n < n!.
#n (cases n) 
  [#H @False_ind /2/ 
  |#m #lt2 normalize @(lt_to_le_to_lt ? (2*(S m))) //
   @le_times // @le_2_fact /2 by lt_plus_to_lt_l/ 
qed.

(* approximations *)

theorem fact_to_exp1: ∀n.O<n →
 (2*n)! ≤ (2^(pred (2*n))) * n! * n!.
#n #posn (cut (∀i.2*(S i) = S(S(2*i)))) [//] #H (elim posn) //
#n #posn #Hind @(transitive_le ? ((2*n)!*(2*(S n))*(2*(S n))))
  [>H normalize @le_times //
  |cut (pred (2*(S n)) = S(S(pred(2*n))))
    [>S_pred // @(le_times 1 ? 1) //] #H1
   cut (2^(pred (2*(S n))) = 2^(pred(2*n))*2*2) 
    [>H1 >H1 //] #H2 >H2
   @(transitive_le ? ((2^(pred (2*n))) * n! * n! *(2*(S n))*(2*(S n))))
    [@le_times[@le_times //]//
    (* we generalize to hide the computational content *)
    |normalize in match ((S n)!); generalize in match (S n);
     #Sn generalize in match 2; #two //
    ]
  ]
qed.  

theorem fact_to_exp: ∀n.
 (2*n)! ≤ (2^(pred (2*n))) * n! * n!.
#n (cases n) [normalize // |#n @fact_to_exp1 //]
qed.

theorem exp_to_fact1: ∀n.O < n →
  2^(2*n)*n!*n! < (S(2*n))!.
#n #posn (elim posn) [normalize //]
#n #posn #Hind (cut (∀i.2*(S i) = S(S(2*i)))) [//] #H
cut (2^(2*(S n)) = 2^(2*n)*2*2) [>H //] #H1 >H1
@(le_to_lt_to_lt ? (2^(2*n)*n!*n!*(2*(S n))*(2*(S n))))
  [normalize in match ((S n)!); generalize in match (S n); #Sn
   generalize in match 2; #two //
  |cut ((S(2*(S n)))! = (S(2*n))!*(S(S(2*n)))*(S(S(S(2*n)))))
   [>H //] #H2 >H2 @lt_to_le_to_lt_times
     [@lt_to_le_to_lt_times //|>H // | //]
  ]
qed.

(* a sligtly better result *)
theorem exp_to_fact2: ∀n.O < n →
  (exp 2 (2*n))*(exp (fact n) 2) \le 2*n*fact (2*n).
#n #posn elim posn
  [@le_n
  |#m #le1m #Hind 
   cut (2*(S m) = S(S (2*m))) [normalize //] #H2 >H2 in ⊢ (?%?);
   >factS <times_exp 
   whd in match (exp 2 (S(S ?))); >(commutative_times ? 2) >associative_times
   >associative_times in ⊢ (??%); @monotonic_le_times_r 
   whd in match (exp 2 (S ?)); >(commutative_times ? 2) >associative_times
   @(transitive_le ? (2*((2*m*(2*m)!)*(S m)^2)))
    [@le_times [//] >commutative_times in ⊢ (?(??%)?); <associative_times
     @le_times [@Hind |@le_n] 
    |>exp_2 <associative_times <associative_times >commutative_times in ⊢ (??%);
     @le_times [2:@le_n] >H2 >factS >commutative_times <associative_times 
     @le_times //
    ]
  ]
qed.

theorem le_fact_10: fact (2*5) ≤ (exp 2 ((2*5)-2))*(fact 5)*(fact 5).
>factS in ⊢ (?%?); >factS in ⊢ (?%?); <associative_times in ⊢ (?%?);
>factS in ⊢ (?%?); <associative_times in ⊢ (?%?);
>factS in ⊢ (?%?); <associative_times in ⊢ (?%?);
>factS in ⊢ (?%?); <associative_times in ⊢ (?%?);
@le_times [2:%] @leb_true_to_le % 
qed-.

theorem ab_times_cd: ∀a,b,c,d.(a*b)*(c*d)=(a*c)*(b*d). 
//
qed.

(* an even better result *)
theorem lt_4_to_fact: ∀n.4<n →
  fact (2*n) ≤ (exp 2 ((2*n)-2))*(fact n)*(fact n).
#n #ltn elim ltn
  [@le_fact_10
  |#m #lem #Hind 
   cut (2*(S m) = S(S (2*m))) [normalize //] #H2 >H2 
   whd in match (minus (S(S ?)) 2); <minus_n_O
   >factS >factS <associative_times >factS
   @(transitive_le ? ((2*(S m))*(2*(S m))*(fact (2*m))))
    [@le_times [2:@le_n] >H2 @le_times //
    |@(transitive_le ? (2*S m*(2*S m)*(2\sup(2*m-2)*m!*m!)))
      [@monotonic_le_times_r //
      |>associative_times >ab_times_cd in ⊢ (?(??%)?);
       <associative_times @le_times [2:@le_n] 
       <associative_times in ⊢ (?(??%)?);
       >ab_times_cd @le_times [2:@le_n] >commutative_times
       >(commutative_times 2) @(le_exp (S(S ((2*m)-2)))) [//]
       >eq_minus_S_pred >S_pred 
        [>eq_minus_S_pred >S_pred [<minus_n_O @le_n |elim lem //]
        |elim lem [//] #m0 #le5m0 #Hind 
         normalize <plus_n_Sm //
        ]
      ]
    ]
  ]
qed. 
