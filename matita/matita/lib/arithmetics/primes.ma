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

include "arithmetics/factorial.ma".
include "arithmetics/minimization.ma".

inductive divides (n,m:nat) : Prop ≝
quotient: ∀q:nat.m = times n q → divides n m.

interpretation "divides" 'divides n m = (divides n m).
interpretation "not divides" 'ndivides n m = (Not (divides n m)).

theorem reflexive_divides : reflexive nat divides.
/2/ qed.

theorem divides_to_div_mod_spec :
∀n,m. O < n → n ∣ m → div_mod_spec m n (m / n) O.
#n #m #posn * #q #eqm % // >eqm 
>commutative_times >div_times //
qed.

theorem div_mod_spec_to_divides :
∀n,m,q. div_mod_spec m n q O → n ∣ m.
#n #m #q * #posn #eqm /2/
qed.

theorem divides_to_mod_O:
∀n,m. O < n → n ∣ m → (m \mod n) = O.
#n #m #posn #divnm 
@(div_mod_spec_to_eq2 m n (m / n) (m \mod n) (m / n) O) /2/ 
qed.

theorem mod_O_to_divides:
∀n,m. O < n → (m \mod n) = O →  n ∣ m. 
/2/ qed.

theorem divides_n_O: ∀n:nat. n ∣ O.
/2/ qed.

theorem divides_n_n: ∀n:nat. n ∣ n.
/2/ qed.

theorem divides_SO_n: ∀n:nat. 1 ∣ n.
/2/ qed.

theorem divides_plus: ∀n,p,q:nat. 
n ∣ p → n ∣ q → n ∣ p+q.
#n #p #q * #d1 #H * #d2 #H1 @(quotient ?? (d1+d2))
>H >H1 //
qed.

theorem divides_minus: ∀n,p,q:nat. 
n ∣ p → n ∣ q → n ∣ (p-q).
#n #p #q * #d1 #H * #d2 #H1 @(quotient ?? (d1-d2))
>H >H1 //
qed.

theorem divides_times: ∀n,m,p,q:nat. 
n ∣ p → m ∣ q → n*m ∣ p*q.
#n #m #p #q * #d1 #H * #d2 #H1 @(quotient ?? (d1*d2))
>H >associative_times >associative_times @eq_f //
qed.

theorem transitive_divides: transitive ? divides.
#a #b #c * #d1 #H * #d2 #H1 @(quotient ?? (d1*d2)) 
>H1 >H //
qed.

theorem eq_mod_to_divides: ∀n,m,q. O < q →
  mod n q = mod m q → q ∣ (n-m).
#n #m #q #posq #eqmod @(leb_elim n m) #nm
  [cut (n-m=O) /2/
  |@(quotient ?? ((div n q)-(div m q)))
   >distributive_times_minus >commutative_times
   >(commutative_times q) cut((n/q)*q = n - (n \mod q)) [//] #H
   >H >minus_plus >eqmod >commutative_plus 
   <div_mod //
  ]
qed.

theorem divides_to_le : ∀n,m. O < m → n ∣ m → n ≤ m.
#n #m #posm * #d (cases d) 
  [#eqm @False_ind /2/ |#p #eqm >eqm // ]
qed.

theorem antisymmetric_divides: ∀n,m. n ∣ m → m ∣ n → n = m.
#n #m #divnm #divmn (cases (le_to_or_lt_eq … (le_O_n n))) #Hn
  [(cases (le_to_or_lt_eq … (le_O_n m))) #Hm
    [@le_to_le_to_eq @divides_to_le //
    |<Hm (cases divmn) //
    ]
  |<Hn (cases divnm) //
  ]
qed.  

theorem divides_to_lt_O : ∀n,m. O < m → n ∣ m → O < n.
#n #m #posm (cases (le_to_or_lt_eq … (le_O_n n))) //
#eqn0 * #d <eqn0 #eqm @False_ind @(absurd …posm) 
@le_to_not_lt > eqm //
qed.

(*a variant of or_div_mod *)
theorem or_div_mod1: ∀n,q. O < q →
  q ∣ S n ∧ S n = S (n/q) * q ∨
  q ∤ S n ∧ S n= (div n q) * q + S (n\mod q).
#n #q #posq cases(or_div_mod n q posq) * #H1 #H2
  [%1 % /2/
  |%2 % // @(not_to_not ? ? (divides_to_mod_O … posq))
   cut (S n \mod q = S(n \mod q)) 
    [@(div_mod_spec_to_eq2 (S n) q (S n/q) (S n \mod q) (n/q) (S (n \mod q))) /2/]
   #Hcut >Hcut % /2/
  ]
qed.

theorem divides_to_div: ∀n,m.n ∣m → m/n*n = m.
#n #m #divnm (cases (le_to_or_lt_eq O n (le_O_n n))) #H
  [>(plus_n_O (m/n*n)) <(divides_to_mod_O ?? H divnm) //
  |(cases divnm) #d <H //
  ]
qed.

theorem divides_div: ∀d,n. d ∣ n → n/d ∣ n.
#d #n #divdn @(quotient ?? d) @sym_eq /2/
qed.

theorem div_div: ∀n,d:nat. O < n → d ∣ n → n/(n/d) = d.
#n #d #posn #divdn @(injective_times_l (n/d))
  [@(lt_times_n_to_lt_l d) >divides_to_div //
  |>divides_to_div 
    [>commutative_times >divides_to_div //
    |@(quotient ? ? d) @sym_eq /2/
    ]
  ]
qed.

theorem times_div: ∀a,b,c:nat.
  O < b → c ∣ b → a * (b /c) = (a*b)/c.
#a #b #c #posb #divcb 
cut(O < c) [@(divides_to_lt_O … posb divcb)] #posc
(cases divcb) #d #eqb >eqb
>(commutative_times c d) >(div_times d c posc) <associative_times
>(div_times (a * d) c posc) // 
qed.

theorem plus_div: ∀n,m,d. O < d →
  d ∣ n → d ∣ m → (n + m) / d = n/d + m/d.
#n #m #d #posd #divdn #divdm
(cases divdn) #a #eqn (cases divdm) #b #eqm
>eqn >eqm <distributive_times_plus >commutative_times
>div_times // >commutative_times >div_times //
>commutative_times >div_times //
qed.

(* boolean divides *)
definition dividesb : nat → nat → bool ≝
λn,m :nat. (eqb (m \mod n) O).

theorem dividesb_true_to_divides:
∀n,m:nat. dividesb n m = true → n ∣ m.
#n #m (cases (le_to_or_lt_eq … (le_O_n n)))
  [#posn #divbnm @mod_O_to_divides // @eqb_true_to_eq @divbnm 
  |#eqnO <eqnO normalize #eqbmO >(eqb_true_to_eq … eqbmO) //
  ]
qed.

theorem dividesb_false_to_not_divides:
∀n,m:nat. dividesb n m = false → n ∤ m.
#n #m (cases (le_to_or_lt_eq … (le_O_n n)))
  [#posn #ndivbnm @(not_to_not ?? (divides_to_mod_O … posn))
   @eqb_false_to_not_eq @ndivbnm
  |#eqnO <eqnO normalize 
   @(nat_case m) [normalize /2/ |#a #_ #_ % * /2/]
  ]
qed.

theorem decidable_divides: ∀n,m:nat. decidable (n ∣ m).
#n #m cases(true_or_false (dividesb n m)) /3/
qed.

theorem divides_to_dividesb_true : ∀n,m:nat. O < n →
  n ∣m → dividesb n m = true.
#n #m #posn #divnm cases(true_or_false (dividesb n m)) //
#ndivbnm @False_ind @(absurd … divnm) /2/
qed.

theorem divides_to_dividesb_true1 : ∀n,m:nat.O < m → 
  n ∣m → dividesb n m = true.
#n #m #posn cases (le_to_or_lt_eq O n (le_O_n n)) /2/
#eqn0 <eqn0 * #q #eqm @False_ind /2/
qed.

theorem not_divides_to_dividesb_false: ∀n,m:nat. O < n →
  n ∤ m → dividesb n m = false.
#n #m #posn cases(true_or_false (dividesb n m)) /2/
#divbnm #ndivnm @False_ind @(absurd ?? ndivnm) /2/
qed.

theorem dividesb_div_true: 
∀d,n. O < n → 
  dividesb d n = true → dividesb (n/d) n = true.
#d #n #posn #divbdn @divides_to_dividesb_true1 //
@divides_div /2/
qed.

theorem dividesb_true_to_lt_O: ∀n,m. 
  O < n → m ∣ n → O < m.
#n #m #posn * #d cases (le_to_or_lt_eq ? ? (le_O_n m)) // 
qed.

(* divides and pi move away ??
theorem divides_f_pi_f : ∀f:nat → nat.∀n,i:nat. 
  i < n → f i ∣ \big[times,0]_{x < n | true}(f x).
#f #n #i (elim n) 
  [#ltiO @False_ind /2/
  |#n #Hind #lti >bigop_Strue // 
   cases(le_to_or_lt_eq …(le_S_S_to_le … lti)) /3/
  ]
*)

(* prime *)
definition prime : nat → Prop ≝
λn:nat. 1 < n ∧ (∀m:nat. m ∣ n → 1 < m → m = n).

theorem not_prime_O: ¬ (prime O).
% * #lt10 /2/
qed.

theorem not_prime_SO: ¬ (prime 1).
% * #lt11 /2/
qed.

theorem prime_to_lt_O: ∀p. prime p → O < p.
#p * #lt1p /2/ 
qed.

theorem prime_to_lt_SO: ∀p. prime p → 1 < p.
#p * #lt1p /2/ 
qed.

(* smallest factor *)
definition smallest_factor : nat → nat ≝
λn:nat. if leb n 1 then n else min n 2 (λm.(eqb (n \mod m) O)).

theorem smallest_factor_to_min : ∀n. 1 < n → 
smallest_factor n = (min n 2 (λm.(eqb (n \mod m) O))).
#n #lt1n normalize >lt_to_leb_false //
qed.

example example1 : smallest_factor 3 = 3.
normalize //
qed.

example example2: smallest_factor 4 = 2.
normalize //
qed.

example example3 : smallest_factor 7 = 7.
normalize //
qed. 

theorem le_SO_smallest_factor: ∀n:nat. 
  n ≤ 1 → smallest_factor n = n.
#n #le1n normalize >le_to_leb_true //
qed.

theorem lt_SO_smallest_factor: ∀n:nat. 
  1 < n → 1 < smallest_factor n.
#n #lt1n >smallest_factor_to_min //
qed.

theorem lt_O_smallest_factor: ∀n:nat. 
  O < n → O < (smallest_factor n).
#n #posn (cases posn) 
  [>le_SO_smallest_factor //
  |#m #posm @le_S_S_to_le @le_S @lt_SO_smallest_factor @le_S_S //
  ]
qed.

theorem divides_smallest_factor_n : ∀n:nat. 0 < n → 
  smallest_factor n ∣ n.
#n #posn (cases (le_to_or_lt_eq … posn)) 
  [#lt1n @mod_O_to_divides [@lt_O_smallest_factor //] 
   >smallest_factor_to_min // @eqb_true_to_eq @f_min_true
   @(ex_intro … n) % /2/ 
  |#H <H //
  ]
qed.
  
theorem le_smallest_factor_n : ∀n.
  smallest_factor n ≤ n.
#n (cases n) // #m @divides_to_le /2/
qed.

theorem lt_smallest_factor_to_not_divides: ∀n,i:nat. 
1 < n → 1 < i → i < smallest_factor n → i ∤ n.
#n #i #ltn #lti >smallest_factor_to_min // #ltmin 
@(not_to_not ? (n \mod i = 0))
  [#divin @divides_to_mod_O /2/
  |@eqb_false_to_not_eq @(lt_min_to_false … lti ltmin)
  ]
qed.

theorem prime_smallest_factor_n : ∀n. 1 < n → 
  prime (smallest_factor n).
#n #lt1n (cut (0<n)) [/2/] #posn % (* bug? *) [/2/] #m #divmmin #lt1m
@le_to_le_to_eq
  [@divides_to_le // @lt_O_smallest_factor //
  |>smallest_factor_to_min // @true_to_le_min //
   @eq_to_eqb_true @divides_to_mod_O /2/ 
   @(transitive_divides … divmmin) @divides_smallest_factor_n //
  ]
qed.

theorem prime_to_smallest_factor: ∀n. prime n →
  smallest_factor n = n.
#n * #lt1n #primen @primen 
  [@divides_smallest_factor_n /2/
  |@lt_SO_smallest_factor //
  ]
qed.

theorem smallest_factor_to_prime: ∀n. 1 < n →
  smallest_factor n = n → prime n.
#n #lt1n #H <H /2/ 
qed.

(* a number n > O is prime iff its smallest factor is n *)
definition primeb ≝ λn:nat.
  (leb 2 n) ∧ (eqb (smallest_factor n) n).

(* it works! *)
example example4 : primeb 3 = true.
normalize // qed.

example example5 : primeb 6 = false.
normalize // qed.

example example6 : primeb 11 = true.
normalize // qed.

example example7 : primeb 17 = true.
normalize // qed.

theorem primeb_true_to_prime : ∀n:nat.
  primeb n = true → prime n.
#n #primebn @smallest_factor_to_prime
  [@leb_true_to_le @(andb_true_l … primebn)
  |@eqb_true_to_eq @( andb_true_r … primebn)
  ]
qed.

theorem primeb_false_to_not_prime : ∀n:nat.
  primeb n = false → ¬ (prime n).
#n #H cut ((leb 2 n ∧ (eqb (smallest_factor n) n)) = false) [@H] 
@leb_elim 
  [#_ #H1 @(not_to_not … (prime_to_smallest_factor … ))
   @eqb_false_to_not_eq @H1
  |#len1 #_ @(not_to_not … len1) * //
  ]
qed.

theorem decidable_prime : ∀n:nat.decidable (prime n).
#n cases(true_or_false (primeb n)) #H 
  [%1 /2/ |%2 /2/]
qed.

theorem prime_to_primeb_true: ∀n:nat. 
  prime n → primeb n = true.
#n #primen (cases (true_or_false (primeb n))) //
#H @False_ind @(absurd … primen) /2/
qed.

theorem not_prime_to_primeb_false: ∀n:nat. 
 ¬(prime n) → primeb n = false.
#n #np (cases (true_or_false (primeb n))) //
#p @False_ind @(absurd (prime n) (primeb_true_to_prime …) np) //
qed.

(* enumeration of all primes *)

theorem divides_fact : ∀n,i:nat. O < i → 
  i ≤ n → i ∣ n!.
#n #i #ltOi (elim n) 
  [#leiO @False_ind @(absurd … ltOi) /2/
  |#n #Hind #lei normalize cases(le_to_or_lt_eq … lei)
    [#ltiS @(transitive_divides ? n!) [@Hind /2/ | /2/]
    |#eqi >eqi /2/
    ]
  ]
qed.

theorem mod_S_fact: ∀n,i:nat. 
  1 < i → i ≤ n → (S n!) \mod i = 1.
#n #i #lt1i #lein
cut(O<i) [/2/] #posi
cut (n! \mod i = O) [@divides_to_mod_O // @divides_fact //] #Hcut
<Hcut @mod_S //
qed.

theorem not_divides_S_fact: ∀n,i:nat. 
  1 < i → i ≤ n → i ∤  S n!.
#n #i #lt1i #lein @(not_to_not … (divides_to_mod_O i (S n!) ?)) /2/
>mod_S_fact // @eqb_false_to_not_eq //
qed.

theorem smallest_factor_fact: ∀n:nat.
  n < smallest_factor (S n!).
#n @not_le_to_lt @(not_to_not ? ((smallest_factor (S n!)) ∤ (S n!)))
  [@not_divides_S_fact @lt_SO_smallest_factor @le_S_S //
  |% * #H @H @divides_smallest_factor_n @le_S_S //
  ]
qed.

theorem ex_prime: ∀n. 1 ≤ n →∃m.
  n < m ∧ m ≤ S n! ∧ (prime m).
#n #lein (cases lein)
  [@(ex_intro nat ? 2) % [/2/|@primeb_true_to_prime //]
  |#m #leim @(ex_intro nat ? (smallest_factor (S (S m)!)))
   % [% [@smallest_factor_fact |@le_smallest_factor_n ]
     |@prime_smallest_factor_n @le_S_S //
     ]
  ] 
qed. 

let rec nth_prime n ≝ match n with
  [ O ⇒ 2
  | S p ⇒
    let previous_prime ≝ nth_prime p in
    let upper_bound ≝ S previous_prime! in
    min upper_bound (S previous_prime) primeb].

lemma nth_primeS: ∀n.nth_prime (S n) = 
   (let previous_prime ≝ nth_prime n in
    let upper_bound ≝ S previous_prime! in
    min upper_bound (S previous_prime) primeb).
// qed.
    
(* it works *)
example example11 : nth_prime 2 = 5.
normalize // qed.

example example12: nth_prime 3 = 7.
normalize //
qed.

example example13 : nth_prime 4 = 11.
normalize // qed.

(* done in 13.1369330883s -- qualcosa non va: // lentissimo 
theorem example14 : nth_prime 18 = 67.
normalize // (* @refl *)
qed.
*)

theorem prime_nth_prime : ∀n:nat.prime (nth_prime n).
#n (cases n) 
  [@primeb_true_to_prime //
  |#m >nth_primeS @primeb_true_to_prime @(f_min_true primeb)
   @(ex_intro nat ? (smallest_factor (S (nth_prime m)!)))
   % [% // @le_S_S @(transitive_le … (le_smallest_factor_n …))
      <plus_n_Sm @le_plus_n_r
     ]
   @prime_to_primeb_true @prime_smallest_factor_n @le_S_S //
  ]
qed.

(* properties of nth_prime *)
theorem increasing_nth_prime: ∀n. nth_prime n < nth_prime (S n).
#n 
change with
(let previous_prime ≝ (nth_prime n) in
 let upper_bound ≝ S previous_prime! in
 S previous_prime ≤ min upper_bound (S previous_prime) primeb)
@le_min_l
qed.

theorem lt_SO_nth_prime_n : ∀n:nat. 1 < nth_prime n.
#n @prime_to_lt_SO //
qed.

theorem lt_O_nth_prime_n : ∀n:nat. O < nth_prime n.
#n @prime_to_lt_O //
qed.

theorem lt_n_nth_prime_n : ∀n:nat. n < nth_prime n.
#n (elim n)
  [@lt_O_nth_prime_n
  |#m #ltm @(le_to_lt_to_lt … ltm) //
  ]
qed.

(*
theorem ex_m_le_n_nth_prime_m: 
∀n.nth_prime O ≤ n → 
∃m. nth_prime m ≤ n ∧ n < nth_prime (S m).
intros.
apply increasing_to_le2.
exact lt_nth_prime_n_nth_prime_Sn.assumption.
qed. *)

theorem lt_nth_prime_to_not_prime: ∀n,m. 
  nth_prime n < m → m < nth_prime (S n) → ¬ (prime m).
#n #m #ltml >nth_primeS #ltmr @primeb_false_to_not_prime
@(lt_min_to_false ? (S (nth_prime n)!) m (S (nth_prime n))) //
qed.

(* nth_prime enumerates all primes *)
theorem prime_to_nth_prime : ∀p:nat. 
  prime p → ∃i.nth_prime i = p.
#p #primep
cut (∃m. nth_prime m ≤ p ∧ p < nth_prime (S m))
 [@(increasing_to_le2 nth_prime ?) // @prime_to_lt_SO //
 |* #n * #lepl #ltpr cases(le_to_or_lt_eq … lepl)
   [#ltpl @False_ind @(absurd … primep)
    @(lt_nth_prime_to_not_prime n p ltpl ltpr)
   |#eqp @(ex_intro … n) //
   ]
 ]
qed.
 
