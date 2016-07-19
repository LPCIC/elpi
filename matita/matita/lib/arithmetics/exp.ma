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

include "arithmetics/div_and_mod.ma".

let rec exp n m on m ≝ 
 match m with 
 [ O ⇒ 1
 | S p ⇒ (exp n p) * n].

interpretation "natural exponent" 'exp a b = (exp a b).

theorem exp_plus_times : ∀n,p,q:nat. 
  n^(p + q) = n^p * n^q.
#n #p #q elim p normalize //
qed.

theorem exp_n_O : ∀n:nat. 1 = n^O. 
//
qed.

theorem exp_n_1 : ∀n:nat. n = n^1. 
#n normalize //
qed.

theorem exp_1_n : ∀n:nat. 1 = 1^n.
#n (elim n) normalize //
qed.

theorem exp_2: ∀n. n^2 = n*n. 
#n normalize //
qed.

theorem exp_exp_times : ∀n,p,q:nat. 
  (n^p)^q = n^(p * q).
#n #p #q (elim q) normalize 
(* [applyS exp_n_O funziona ma non lo trova *)
// <times_n_O // 
qed.

theorem lt_O_exp: ∀n,m:nat. O < n → O < n^m. 
#n #m (elim m) normalize // #a #Hind #posn 
@(le_times 1 ? 1) /2/ qed.

(* [applyS monotonic_le_minus_r /2/ 

> (minus_Sn_n ?) 
[cut (∃x.∃y.∃z.(x - y ≤ x - z) = (1 ≤ n ^a))
  [@ex_intro
    [|@ex_intro
      [|@ex_intro
        [|     
@(rewrite_r \Nopf  (S  n \sup a - n \sup a )
 (\lambda x:\Nopf 
  .(S  n \sup a - n \sup a \le S  n \sup a -(S ?-?))=(x\le  n \sup a ))
 (rewrite_r \Nopf  ?
  (\lambda x:\Nopf 
   .(S  n \sup a - n \sup a \le x)=(S  n \sup a - n \sup a \le  n \sup a ))
  ( refl … Type[0]  (S  n \sup a - n \sup a \le  n \sup a ) ) (S ?-(S ?-?))
  (rewrite_r \Nopf  (?-O) (\lambda x:\Nopf .S ?-(S ?-?)=x)
   (rewrite_l \Nopf  1 (\lambda x:\Nopf .S ?-x=n ^a -O) (minus_S_S ? O) (S ?-?)
    (minus_Sn_n ?)) ?
   (minus_n_O ?))) 1
 (minus_Sn_n  n \sup a ))  
         
@(rewrite_r \Nopf  (S ?-?)
 (\lambda x:\Nopf 
  .(S  n \sup a - n \sup a \le S  n \sup a -(S ?-?))=(x\le  n \sup a ))
 (rewrite_r \Nopf  ?
  (\lambda x:\Nopf 
   .(S  n \sup a - n \sup a \le x)=(S  n \sup a - n \sup a \le  n \sup a ))
  ( refl ??) (S ?-(S ?-?))
  ?) 1
 (minus_Sn_n ?))
  [||
@(rewrite_r \Nopf  (?-O) (\lambda x:\Nopf .S ?-(S ?-?)=x)
  ???)
[|<(minus_Sn_n ?)
@(rewrite_r \Nopf  (?-O) (\lambda x:\Nopf .S ?-(S ?-?)=x)
 (rewrite_l \Nopf  1 (\lambda x:\Nopf .S ?-x=?-O) 
    ? (S ?-?)
    (minus_Sn_n ?)) ??)
 
@(rewrite_r \Nopf  (?-O) (\lambda x:\Nopf .S ?-(S ?-?)=x)
   (rewrite_l \Nopf  1 (\lambda x:\Nopf .S ?-x=?-O) (minus_S_S ? O) (S ?-?)
    (minus_Sn_n ?)) ?
   (minus_n_O ?)))

applyS monotonic_le_minus_r /2/
qed. *)

theorem lt_m_exp_nm: ∀n,m:nat. 1 < n → m < n^m.
#n #m #lt1n (elim m) normalize // 
#n #Hind @(transitive_le ? ((S n)*2)) // @le_times //
qed.

theorem exp_to_eq_O: ∀n,m:nat. 1 < n → 
  n^m = 1 → m = O.
#n #m #ltin #eq1 @le_to_le_to_eq //
@le_S_S_to_le <eq1 @lt_m_exp_nm //
qed.

theorem injective_exp_r: ∀b:nat. 1 < b → 
  injective nat nat (λi:nat. b^i).
#b #lt1b @nat_elim2 normalize 
  [#n #H @sym_eq @(exp_to_eq_O b n lt1b) //
  |#n #H @False_ind @(absurd (1 < 1) ? (not_le_Sn_n 1))
   <H in ⊢ (??%); @(lt_to_le_to_lt ? (1*b)) //
   @le_times // @lt_O_exp /2/
  |#n #m #Hind #H @eq_f @Hind @(injective_times_l … H) /2/
  ]
qed.

theorem le_exp: ∀n,m,p:nat. O < p →
  n ≤m → p^n ≤ p^m.
@nat_elim2 #n #m
  [#ltm #len @lt_O_exp //
  |#_ #len @False_ind /2/
  |#Hind #p #posp #lenm normalize @le_times // @Hind /2/
  ]
qed.

theorem le_exp1: ∀n,m,a:nat. O < a →
  n ≤m → n^a ≤ m^a.
#n #m #a #posa #lenm (elim posa) //
#a #posa #Hind @le_times //
qed.

theorem lt_exp: ∀n,m,p:nat. 1 < p → 
  n < m → p^n < p^m.
#n #m #p #lt1p #ltnm 
cut (p \sup n ≤ p \sup m) [@le_exp /2/] #H 
cases(le_to_or_lt_eq … H) // #eqexp
@False_ind @(absurd (n=m)) /2/
qed.

theorem lt_exp1: ∀n,m,p:nat. 0 < p → 
  n < m → n^p < m^p.
#n #m #p #posp #ltnm (elim posp) //
#p #posp #Hind @lt_times //
qed.
  
theorem le_exp_to_le: 
∀b,n,m. 1 < b → b^n ≤ b^m → n ≤ m.
#b #n #m #lt1b #leexp cases(decidable_le n m) //
#notle @False_ind @(absurd … leexp) @lt_to_not_le
@lt_exp /2/
qed.

theorem le_exp_to_le1 : ∀n,m,p.O < p → 
  n^p ≤ m^p → n ≤ m.
#n #m #p #posp #leexp @not_lt_to_le 
@(not_to_not … (lt_exp1 ??? posp)) @le_to_not_lt // 
qed.
     
theorem lt_exp_to_lt: 
∀a,n,m. 0 < a → a^n < a^m → n < m.
#a #n #m #lt1a #ltexp cases(decidable_le (S n) m) //
#H @False_ind @(absurd … ltexp) @le_to_not_lt 
@le_exp // @not_lt_to_le @H
qed.

theorem lt_exp_to_lt1: 
∀a,n,m. O < a → n^a < m^a → n < m.
#a #n #m #posa #ltexp cases(decidable_le (S n) m) //
#H @False_ind @(absurd … ltexp) @le_to_not_lt 
@le_exp1 // @not_lt_to_le @H 
qed.
     
theorem times_exp: ∀n,m,p. 
  n^p * m^p = (n*m)^p.
#n #m #p (elim p) // #p #Hind normalize //
qed.

  
   
   