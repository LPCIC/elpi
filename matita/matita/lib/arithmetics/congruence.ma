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

definition S_mod ≝ λn,m:nat. S m \mod n.

definition congruent ≝ λn,m,p:nat. mod n p = mod m p.

notation "hvbox(n break ≅_{p} m)"
  non associative with precedence 45
for @{ 'congruent $n $m $p }.

interpretation "congruent" 'congruent n m p = (congruent n m p).

theorem congruent_n_n: ∀n,p:nat.congruent n n p.
// qed.

theorem transitive_congruent: ∀p. transitive ? (λn,m. congruent n m p).
// qed.

theorem le_to_mod: ∀n,m:nat. n < m → n = n \mod m.
#n #m #ltnm @(div_mod_spec_to_eq2 n m O n (n/m) (n \mod m))
% // @lt_mod_m_m @(ltn_to_ltO … ltnm) 
qed.

theorem mod_mod : ∀n,p:nat. O<p → n \mod p = (n \mod p) \mod p.
#n #p #posp >(div_mod (n \mod p) p) in ⊢ (??%?);
>(eq_div_O ? p) // @lt_mod_m_m //
qed.

theorem mod_times_mod : ∀n,m,p:nat. O<p → O<m → 
  n \mod p = (n \mod (m*p)) \mod p.
#n #m #p #posp #posm 
@(div_mod_spec_to_eq2 n p (n/p) (n \mod p) (n/(m*p)*m + (n \mod (m*p)/p)))
  [@div_mod_spec_div_mod //
  |% [@lt_mod_m_m //]
   >distributive_times_plus_r >associative_plus <div_mod //
  ]
qed.

theorem congruent_n_mod_n: ∀n,p. 0 < p → 
  congruent n (n \mod p) p.
#n #p #posp @mod_mod //
qed.

theorem congruent_n_mod_times: ∀n,m,p. 0 < p → 0 < m → 
  congruent n (n \mod (m*p)) p.
#n #p #posp @mod_times_mod 
qed.

theorem eq_times_plus_to_congruent: ∀n,m,p,r:nat. 0 < p → 
  n = r*p+m → congruent n m p.
#n #m #p #r #posp #Hn
@(div_mod_spec_to_eq2 n p (div n p) (mod n p) (r +(div m p)) (mod m p))
  [@div_mod_spec_div_mod //
  |% [@lt_mod_m_m //]
   >commutative_times >distributive_times_plus >commutative_times 
   >(commutative_times p) >associative_plus //
  ]
qed.

theorem divides_to_congruent: ∀n,m,p:nat. 0 < p → m ≤ n → 
  divides p (n - m) → congruent n m p.
#n #m #p #posp #lemn * #q #Hdiv @(eq_times_plus_to_congruent n m p q) //
>commutative_plus @minus_to_plus //
qed.

theorem congruent_to_divides: ∀n,m,p:nat.
  0 < p → congruent n m p → divides p (n - m).
#n #m #p #posp #Hcong %{((n / p)-(m / p))}
>commutative_times >(div_mod n p) in ⊢ (??%?);
>(div_mod m p) in ⊢ (??%?); //
qed.

theorem mod_times: ∀n,m,p. 0 < p → 
  mod (n*m) p = mod ((mod n p)*(mod m p)) p.
#n #m #p #posp 
@(eq_times_plus_to_congruent ? ? p 
  ((n / p)*p*(m / p) + (n / p)*(m \mod p) + (n \mod p)*(m / p))) //
@(trans_eq ? ? (((n/p)*p+(n \mod p))*((m/p)*p+(m \mod p)))) //
@(trans_eq ? ? (((n/p)*p)*((m/p)*p) + (n/p)*p*(m \mod p) +
  (n \mod p)*((m / p)*p) + (n \mod p)*(m \mod p)))
  [cut (∀a,b,c,d.(a+b)*(c+d) = a*c +a*d + b*c + b*d) 
    [#a #b #c #d >(distributive_times_plus_r (c+d) a b) 
     >(distributive_times_plus a c d)
     >(distributive_times_plus b c d) //] #Hcut 
   @Hcut
  |@eq_f2
    [<associative_times >(associative_times (n/p) p (m \mod p))
     >(commutative_times p (m \mod p)) <(associative_times (n/p) (m \mod p) p)
     >distributive_times_plus_r // 
    |%
    ]
  ]
qed.

theorem congruent_times: ∀n,m,n1,m1,p. O < p → congruent n n1 p → 
  congruent m m1 p → congruent (n*m) (n1*m1) p.
#n #m #n1 #m1 #p #posp #Hcongn #Hcongm whd
>(mod_times n m p posp) >Hcongn >Hcongm @sym_eq @mod_times //
qed.

