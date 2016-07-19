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
include "arithmetics/bigops.ma".

(* Sigma e Pi *)

notation "∑_{ ident i < n | p } f"
  with precedence 80
for @{'bigop $n plus 0 (λ${ident i}. $p) (λ${ident i}. $f)}.

notation "∑_{ ident i < n } f"
  with precedence 80
for @{'bigop $n plus 0 (λ${ident i}.true) (λ${ident i}. $f)}.

notation "∑_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) plus 0 (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "∑_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) plus 0 (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
 
notation "∏_{ ident i < n | p} f"
  with precedence 80
for @{'bigop $n times 1 (λ${ident i}.$p) (λ${ident i}. $f)}.
 
notation "∏_{ ident i < n } f"
  with precedence 80
for @{'bigop $n times 1 (λ${ident i}.true) (λ${ident i}. $f)}.

notation "∏_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) times 1 (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "∏_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) times 1 (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.

(* instances of associative and commutative operations *)

definition plusA ≝ mk_Aop nat 0 plus (λa.refl ? a) (λn.sym_eq ??? (plus_n_O n)) 
   (λa,b,c.sym_eq ??? (associative_plus a b c)).
   
definition plusAC ≝ mk_ACop nat 0 plusA commutative_plus.

definition timesA ≝ mk_Aop nat 1 times 
   (λa.sym_eq ??? (plus_n_O a)) (λn.sym_eq ??? (times_n_1 n)) 
   (λa,b,c.sym_eq ??? (associative_times a b c)).
   
definition timesAC ≝ mk_ACop nat 1 timesA commutative_times.

definition natD ≝ mk_Dop nat 0 plusAC times (λn.(sym_eq ??? (times_n_O n))) 
   distributive_times_plus.
   
(********************************************************)

theorem sigma_const: ∀n:nat. ∑_{i<n} 1 = n.
#n elim n // #n1 >bigop_Strue //
qed.

(* monotonicity; these roperty should be expressed at a more
genral level *)

theorem le_sigma: 
∀n:nat. ∀p1,p2:nat → bool. ∀g1,g2:nat → nat.
(∀i. i < n → p1 i = true → p2 i = true ) → 
(∀i. i < n → p1 i = true → g1 i ≤ g2 i ) → 
 ∑_{i < n | p1 i} (g1 i) ≤ ∑_{i < n | p2 i} (g2 i).
#n #p1 #p2 #g1 #g2 elim n 
  [#_ #_ @le_n
  |#n1 #Hind #H1 #H2 
   lapply (Hind ??)
     [#j #ltin1 #Hgj @(H2 … Hgj) @le_S //
     |#j #ltin1 #Hp1j @(H1 … Hp1j) @le_S //
     ] -Hind #Hind
   cases (true_or_false (p2 n1)) #Hp2
    [>bigop_Strue in ⊢ (??%); [2:@Hp2] 
     cases (true_or_false (p1 n1)) #Hp1
      [>bigop_Strue [2:@Hp1] @(le_plus … Hind) @H2 // 
      |>bigop_Sfalse [2:@Hp1] @le_plus_a // 
      ]
    |cut (p1 n1 = false) 
      [cases (true_or_false (p1 n1)) #Hp1
        [>(H1 … (le_n ?) Hp1) in Hp2; #H destruct (H) | //]
      ] #Hp1
     >bigop_Sfalse [2:@Hp1] >bigop_Sfalse [2:@Hp2] //
    ]
  ]
qed.

theorem lt_sigma_p: 
∀n:nat. ∀p1,p2:nat → bool. ∀g1,g2:nat → nat.
(∀i. i < n → p1 i = true → p2 i = true) →
(∀i. i < n → p1 i = true → g1 i ≤ g2 i ) →
(∃i. i < n ∧ ((p1 i = true) ∧ (g1 i < g2 i)
              ∨ (p1 i = false ∧ (p2 i = true) ∧ (0 < g2 i)))) →
  ∑_{i < n | p1 i} (g1 i) < ∑_{i < n | p2 i} (g2 i).
#n #p1 #p2 #g1 #g2 #H1 #H2 * #k * #ltk * 
  [* #p1k #gk 
   lapply (H1 k ltk p1k) #p2k
   >(bigop_diff p1 ?? plusAC … ltk p1k)
   >(bigop_diff p2 ?? plusAC … ltk p2k) whd 
   cut (∀a,b. S a + b = S(a +b)) [//] #Hplus <Hplus @le_plus
    [@gk
    |@le_sigma
      [#i #ltin #H @true_to_andb_true 
        [@(andb_true_l … H) | @(H1 i ltin) @(andb_true_r … H)]
      |#i #ltin #H @(H2 i ltin) @(andb_true_r … H)
      ]
    ]
  |* * #p1k #p2k #posg2
   >(bigop_diff p2 ?? plusAC … ltk p2k) whd 
   cut (∀a. S 0 + a = S a) [//] #H0 <(H0 (bigop n ?????)) @le_plus
    [@posg2   
    |@le_sigma
      [#i #ltin #H @true_to_andb_true 
        [cases (true_or_false (eqb k i)) #Hc >Hc
          [normalize <H <p1k >(eqb_true_to_eq … Hc) //|//] 
        |@(H1 i ltin) @H]
      |#i #ltin #H @(H2 i ltin) @H
      ]
    ]
qed.
 
theorem le_pi: 
∀n.∀p:nat → bool.∀g1,g2:nat → nat. 
  (∀i.i<n → p i = true → g1 i ≤ g2 i ) → 
  ∏_{i < n | p i} (g1 i) ≤ ∏_{i < n | p i} (g2 i).
#n #p #g1 #g2 elim n 
  [#_ @le_n
  |#n1 #Hind #Hle cases (true_or_false (p n1)) #Hcase
    [ >bigop_Strue // >bigop_Strue // @le_times
      [@Hle // |@Hind #i #lti #Hpi @Hle [@lt_to_le @le_S_S @lti|@Hpi]]
    |>bigop_Sfalse // >bigop_Sfalse // @Hind
     #i #lti #Hpi @Hle [@lt_to_le @le_S_S @lti|@Hpi]
    ]
  ]
qed.

theorem exp_sigma: ∀n,a,p. 
  ∏_{i < n | p i} a = exp a (∑_{i < n | p i} 1).
#n #a #p elim n // #n1 cases (true_or_false (p n1)) #Hcase
  [>bigop_Strue // >bigop_Strue // |>bigop_Sfalse // >bigop_Sfalse //] 
qed.

theorem times_pi: ∀n,p,f,g. 
  ∏_{i<n|p i}(f i*g i) = ∏_{i<n|p i}(f i) * ∏_{i<n|p i}(g i). 
#n #p #f #g elim n // #n1 cases (true_or_false (p n1)) #Hcase #Hind
  [>bigop_Strue // >bigop_Strue // >bigop_Strue //
  |>bigop_Sfalse // >bigop_Sfalse // >bigop_Sfalse //
  ]
qed.

theorem pi_1: ∀n,p. 
  ∏_{i < n | p i} 1 = 1.
#n #p elim n // #n1 #Hind cases (true_or_false (p n1)) #Hc 
  [>bigop_Strue >Hind // |>bigop_Sfalse // ]
qed.

theorem exp_pi: ∀n,m,p,f. 
  ∏_{i < n | p i}(exp (f i) m) = exp (∏_{i < n | p i}(f i)) m.
#n #m #p #f elim m
  [@pi_1
  |#m1 #Hind >times_pi >Hind %
  ]
qed.

theorem exp_sigma_l: ∀n,a,p,f. 
  ∏_{i < n | p i} (exp a (f i)) = exp a (∑_{i < n | p i}(f i)).
#n #a #p #f elim n // #i #Hind cases (true_or_false (p i)) #Hc
  [>bigop_Strue [>bigop_Strue [>Hind >exp_plus_times // |//] |//]
  |>bigop_Sfalse [>bigop_Sfalse [@Hind|//] | //]
  ]
qed.

theorem exp_pi_l: ∀n,a,f. 
  exp a n*(∏_{i < n}(f i)) = ∏_{i < n} (a*(f i)).
#n #a #f elim n // #i #Hind >bigop_Strue // >bigop_Strue //
<Hind <associative_times <associative_times @eq_f2 // normalize // 
qed.

theorem exp_pi_bc: ∀a,b,c,f. 
  exp a (c-b)*(∏_{i ∈ [b,c[ }(f i)) = ∏_{i ∈ [b,c[ } (a*(f i)).
#a #b #c #f @exp_pi_l 
qed.