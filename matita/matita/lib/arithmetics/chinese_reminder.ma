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
include "arithmetics/congruence.ma".

theorem congruent_ab: ∀m,n,a,b:nat. O < n → O < m → 
 gcd n m = 1 → ∃x.x ≅_{m} a ∧ x ≅_{n} b.
#m #n #a #b #posn #posm #pnm
cut (∃c,d.c*n - d*m = 1 ∨ d*m - c*n = 1) [<pnm @eq_minus_gcd]
* #c * #d * #H
  [(* first case *)
   @(ex_intro nat ? ((a+b*m)*c*n-b*d*m)) %
    [(* congruent to a *)
     cut (c*n = d*m + 1)
      [@minus_to_plus // @(transitive_le … (le_n_Sn …)) 
       @(lt_minus_to_plus_r 0) //] -H #H
     >associative_times >H <(commutative_plus ? (d*m))
     >distributive_times_plus <times_n_1 >associative_plus
     <associative_times <distributive_times_plus_r 
     <commutative_plus <plus_minus
       [@(eq_times_plus_to_congruent … posm) //
       |applyS monotonic_le_times_r @(transitive_le ? ((a+b*m)*d)) // 
        applyS monotonic_le_times_r @(transitive_le … (b*m)) /2/
       ]
    |(* congruent to b *)
     -pnm (cut (d*m = c*n-1))
       [@sym_eq @plus_to_minus >commutative_plus 
        @minus_to_plus // @(transitive_le … (le_n_Sn …)) 
     @(lt_minus_to_plus_r 0) //] #H1
     >(associative_times b d) >H1 >distributive_times_minus 
     <associative_times <minus_minus
       [@(eq_times_plus_to_congruent … posn) //
       |applyS monotonic_le_times_r >commutative_times
        @monotonic_le_times_r @(transitive_le ? (m*b)) /2/
       |applyS monotonic_le_times_r @le_plus_to_minus // 
       ]
    ]
  |(* and now the symmetric case; the price to pay for working
      in nat instead than Z *)
   @(ex_intro nat ? ((b+a*n)*d*m-a*c*n)) %
    [(* congruent to a *)
     cut (c*n = d*m - 1) 
       [@sym_eq @plus_to_minus >commutative_plus @minus_to_plus // @(transitive_le … (le_n_Sn …)) 
        @(lt_minus_to_plus_r 0) //] #H1
     >(associative_times a c) >H1
     >distributive_times_minus
     <minus_minus
      [@(eq_times_plus_to_congruent … posm) //
      |<associative_times applyS monotonic_le_times_r
       >commutative_times @monotonic_le_times_r 
       @(transitive_le ? (n*a)) /2/
      |@monotonic_le_times_r <H @le_plus_to_minus //
      ]
    |(* congruent to b *)
     cut (d*m = c*n + 1)
      [@minus_to_plus // @(transitive_le … (le_n_Sn …)) 
       @(lt_minus_to_plus_r 0) //] -H #H
     >associative_times >H
     >(commutative_plus (c*n))
     >distributive_times_plus <times_n_1
     <associative_times >associative_plus 
     <distributive_times_plus_r <commutative_plus <plus_minus
      [@(eq_times_plus_to_congruent … posn) //
      |applyS monotonic_le_times_r @(transitive_le ? (c*(b+n*a))) // 
       <commutative_times @monotonic_le_times_r
       @(transitive_le ? (n*a)) /2/
      ]
    ]
  ]
qed.
       
theorem congruent_ab_lt: ∀m,n,a,b. O < n → O < m → 
gcd n m = 1 → ∃x.x ≅_{m} a ∧ x ≅_{n} b ∧ x < m*n.
#m #n #a #b #posn #posm #pnm
cases(congruent_ab m n a b posn posm pnm) #x * #cxa #cxb
@(ex_intro ? ? (x \mod (m*n))) % 
  [% 
    [@(transitive_congruent m ? x) // 
     @sym_eq >commutative_times @congruent_n_mod_times //
    |@(transitive_congruent n ? x) // 
     @sym_eq @congruent_n_mod_times //
    ]
  |@lt_mod_m_m >(times_n_O 0) @lt_times //
  ]
qed.

definition cr_pair ≝ λn,m,a,b. 
min (n*m) 0 (λx. andb (eqb (x \mod n) a) (eqb (x \mod m) b)).

example cr_pair1: cr_pair 2 3 O O = O.
// qed.

example cr_pair2: cr_pair 2 3 1 0 = 3.
// qed.

example cr_pair3: cr_pair 2 3 1 2 = 5.
// qed.

example cr_pair4: cr_pair 5 7 3 2 = 23.
// qed.

example cr_pair5: cr_pair 3 7 0 4 = ?.
normalize
// qed.

theorem mod_cr_pair : ∀m,n,a,b. a < m → b < n → gcd n m = 1 → 
(cr_pair m n a b) \mod m = a ∧ (cr_pair m n a b) \mod n = b.
#m #n #a #b #ltam #ltbn #pnm 
cut (andb (eqb ((cr_pair m n a b) \mod m) a) 
         (eqb ((cr_pair m n a b) \mod n) b) = true)
  [whd in match (cr_pair m n a b); @f_min_true cases(congruent_ab_lt m n a b ?? pnm)
    [#x * * #cxa #cxb #ltx @(ex_intro ?? x) % /2/
     >eq_to_eqb_true
      [>eq_to_eqb_true // <(lt_to_eq_mod …ltbn) //
      |<(lt_to_eq_mod …ltam) //
      ]
    |@(le_to_lt_to_lt … ltbn) //
    |@(le_to_lt_to_lt … ltam) //
    ]
  |#H >(eqb_true_to_eq … (andb_true_l … H)) >(eqb_true_to_eq … (andb_true_r … H)) /2/
  ]
qed.
