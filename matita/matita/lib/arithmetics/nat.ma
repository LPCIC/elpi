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

include "basics/relations.ma".

(* Definitions **************************************************************)

(* natural numbers *)

inductive nat : Type[0] ≝
  | O : nat
  | S : nat → nat.
  
interpretation "Natural numbers" 'N = nat.

alias num (instance 0) = "natural number".

definition pred ≝
 λn. match n with [ O ⇒ O | S p ⇒ p].

definition not_zero: nat → Prop ≝
 λn: nat. match n with [ O ⇒ False | (S p) ⇒ True ].

(* order relations *)

inductive le (n:nat) : nat → Prop ≝
  | le_n : le n n
  | le_S : ∀ m:nat. le n m → le n (S m).

interpretation "natural 'less or equal to'" 'leq x y = (le x y).

interpretation "natural 'neither less nor equal to'" 'nleq x y = (Not (le x y)).

definition lt: nat → nat → Prop ≝ λn,m. S n ≤ m.

interpretation "natural 'less than'" 'lt x y = (lt x y).

interpretation "natural 'not less than'" 'nless x y = (Not (lt x y)).

definition ge: nat → nat → Prop ≝ λn,m.m ≤ n.

interpretation "natural 'greater or equal to'" 'geq x y = (ge x y).

definition gt: nat → nat → Prop ≝ λn,m.m<n.

interpretation "natural 'greater than'" 'gt x y = (gt x y).

interpretation "natural 'not greater than'" 'ngtr x y = (Not (gt x y)).

(* abstract properties *)

definition increasing ≝ λf:nat → nat. ∀n:nat. f n < f (S n).

(* arithmetic operations *)

let rec plus n m ≝ 
 match n with [ O ⇒ m | S p ⇒ S (plus p m) ].

interpretation "natural plus" 'plus x y = (plus x y).

let rec times n m ≝ 
 match n with [ O ⇒ 0 | S p ⇒ m + (times p m) ].

interpretation "natural times" 'times x y = (times x y).

let rec minus n m ≝ 
 match n with 
 [ O ⇒ O
 | S p ⇒ 
	match m with
	  [ O ⇒ S p
    | S q ⇒ minus p q ]].
        
interpretation "natural minus" 'minus x y = (minus x y).

(* Generic conclusion ******************************************************)

theorem nat_case:
 ∀n:nat.∀P:nat → Prop. 
  (n=O → P O) → (∀m:nat. n= S m → P (S m)) → P n.
#n #P (elim n) /2/ qed.

theorem nat_elim2 :
 ∀R:nat → nat → Prop.
  (∀n:nat. R O n) 
  → (∀n:nat. R (S n) O)
  → (∀n,m:nat. R n m → R (S n) (S m))
  → ∀n,m:nat. R n m.
#R #ROn #RSO #RSS #n (elim n) // #n0 #Rn0m #m (cases m) /2/ qed.

lemma le_gen: ∀P:nat → Prop.∀n.(∀i. i ≤ n → P i) → P n.
/2/ qed.

(* Equalities ***************************************************************)

theorem pred_Sn : ∀n. n = pred (S n).
// qed.

theorem injective_S : injective nat nat S.
// qed.

theorem S_pred: ∀n. 0 < n → S(pred n) = n.
#n #posn (cases posn) //
qed.

theorem plus_O_n: ∀n:nat. n = 0 + n.
// qed.

theorem plus_n_O: ∀n:nat. n = n + 0.
#n (elim n) normalize // qed.

theorem plus_n_Sm : ∀n,m:nat. S (n+m) = n + S m.
#n (elim n) normalize // qed.

theorem commutative_plus: commutative ? plus.
#n (elim n) normalize // qed. 

theorem associative_plus : associative nat plus.
#n (elim n) normalize // qed.

theorem assoc_plus1: ∀a,b,c. c + (b + a) = b + c + a.
// qed. 

theorem injective_plus_r: ∀n:nat.injective nat nat (λm.n+m).
#n (elim n) normalize /3/ qed.

theorem injective_plus_l: ∀n:nat.injective nat nat (λm.m+n). 
/2/ qed.

theorem times_Sn_m: ∀n,m:nat. m+n*m = S n*m.
// qed.

theorem times_O_n: ∀n:nat. 0 = 0 * n.
// qed.

theorem times_n_O: ∀n:nat. 0 = n * 0.
#n (elim n) // qed.

theorem times_n_Sm : ∀n,m:nat. n+(n*m) = n*(S m).
#n (elim n) normalize // qed.

theorem commutative_times : commutative nat times. 
#n (elim n) normalize // qed. 

theorem distributive_times_plus : distributive nat times plus.
#n (elim n) normalize // qed.

theorem distributive_times_plus_r :
  ∀a,b,c:nat. (b+c)*a = b*a + c*a.
// qed. 

theorem associative_times: associative nat times.
#n (elim n) normalize // qed.

lemma times_times: ∀x,y,z. x*(y*z) = y*(x*z).
// qed. 

theorem times_n_1 : ∀n:nat. n = n * 1.
// qed.

theorem minus_S_S: ∀n,m:nat.S n - S m = n -m.
// qed.

theorem minus_O_n: ∀n:nat.0=0-n.
#n (cases n) // qed.

theorem minus_n_O: ∀n:nat.n=n-0.
#n (cases n) // qed.

theorem minus_n_n: ∀n:nat.0=n-n.
#n (elim n) // qed.

theorem minus_Sn_n: ∀n:nat. S 0 = (S n)-n.
#n (elim n) normalize // qed.

theorem eq_minus_S_pred: ∀n,m. n - (S m) = pred(n -m).
@nat_elim2 normalize // qed.

lemma plus_plus_comm_23: ∀x,y,z. x + y + z = x + z + y.
// qed.

lemma discr_plus_xy_minus_xz: ∀x,z,y. x + y = x - z → y = 0.
#x elim x -x // #x #IHx * normalize
[ #y #H @(IHx 0) <minus_n_O /2 width=1/
| #z #y >plus_n_Sm #H lapply (IHx … H) -x -z #H destruct
]
qed-.

(* Negated equalities *******************************************************)

theorem not_eq_S: ∀n,m:nat. n ≠ m → S n ≠ S m.
/2/ qed.

theorem not_eq_O_S : ∀n:nat. 0 ≠ S n.
#n @nmk #eqOS (change with (not_zero O)) >eqOS // qed.

theorem not_eq_n_Sn: ∀n:nat. n ≠ S n.
#n (elim n) /2/ qed.

(* Atomic conclusion *******************************************************)

(* not_zero *)

theorem lt_to_not_zero : ∀n,m:nat. n < m → not_zero m.
#n #m #Hlt (elim Hlt) // qed.

(* le *)

theorem le_S_S: ∀n,m:nat. n ≤ m → S n ≤ S m.
#n #m #lenm (elim lenm) /2/ qed.

theorem le_O_n : ∀n:nat. 0 ≤ n.
#n (elim n) /2/ qed.

theorem le_n_Sn : ∀n:nat. n ≤ S n.
/2/ qed.

theorem transitive_le : transitive nat le.
#a #b #c #leab #lebc (elim lebc) /2/
qed.

theorem le_pred_n : ∀n:nat. pred n ≤ n.
#n (elim n) // qed.

theorem monotonic_pred: monotonic ? le pred.
#n #m #lenm (elim lenm) /2/ qed.

theorem le_S_S_to_le: ∀n,m:nat. S n ≤ S m → n ≤ m.
(* demo *)
/2/ qed-.

theorem monotonic_le_plus_r: 
∀n:nat.monotonic nat le (λm.n + m).
#n #a #b (elim n) normalize //
#m #H #leab @le_S_S /2/ qed.

theorem monotonic_le_plus_l: 
∀m:nat.monotonic nat le (λn.n + m).
/2/ qed.

theorem le_plus: ∀n1,n2,m1,m2:nat. n1 ≤ n2  → m1 ≤ m2 
→ n1 + m1 ≤ n2 + m2.
#n1 #n2 #m1 #m2 #len #lem @(transitive_le ? (n1+m2))
/2/ qed.

theorem le_plus_n :∀n,m:nat. m ≤ n + m.
/2/ qed. 

lemma le_plus_a: ∀a,n,m. n ≤ m → n ≤ a + m.
/2/ qed.

lemma le_plus_b: ∀b,n,m. n + b ≤ m → n ≤ m.
/2/ qed.

theorem le_plus_n_r :∀n,m:nat. m ≤ m + n.
/2/ qed.

theorem eq_plus_to_le: ∀n,m,p:nat.n=m+p → m ≤ n.
// qed-.

theorem le_plus_to_le: ∀a,n,m. a + n ≤ a + m → n ≤ m.
#a (elim a) normalize /3/ qed. 

theorem le_plus_to_le_r: ∀a,n,m. n + a ≤ m +a → n ≤ m.
/2/ qed-. 

theorem monotonic_le_times_r: 
∀n:nat.monotonic nat le (λm. n * m).
#n #x #y #lexy (elim n) normalize//(* lento /2/*)
#a #lea @le_plus //
qed.

theorem le_times: ∀n1,n2,m1,m2:nat. 
n1 ≤ n2  → m1 ≤ m2 → n1*m1 ≤ n2*m2.
#n1 #n2 #m1 #m2 #len #lem @(transitive_le ? (n1*m2)) /2/
qed.

(* interessante *)
theorem lt_times_n: ∀n,m:nat. O < n → m ≤ n*m.
#n #m #H /2/ qed.

theorem le_times_to_le: 
∀a,n,m. O < a → a * n ≤ a * m → n ≤ m.
#a @nat_elim2 normalize
  [//
  |#n #H1 #H2 
     @(transitive_le ? (a*S n)) /2/
  |#n #m #H #lta #le
     @le_S_S @H /2/
  ]
qed-.

theorem le_plus_minus_m_m: ∀n,m:nat. n ≤ (n-m)+m.
#n (elim n) // #a #Hind #m (cases m) // normalize #n/2/  
qed.

theorem le_plus_to_minus_r: ∀a,b,c. a + b ≤ c → a ≤ c -b.
#a #b #c #H @(le_plus_to_le_r … b) /2/
qed.

lemma lt_to_le: ∀x,y. x < y → x ≤ y.
/2 width=2/ qed.

lemma inv_eq_minus_O: ∀x,y. x - y = 0 → x ≤ y.
// qed-.

lemma le_x_times_x: ∀x. x ≤ x * x.
#x elim x -x //
qed.

(* lt *)

theorem transitive_lt: transitive nat lt.
#a #b #c #ltab #ltbc (elim ltbc) /2/
qed.

theorem lt_to_le_to_lt: ∀n,m,p:nat. n < m → m ≤ p → n < p.
#n #m #p #H #H1 (elim H1) /2/ qed.

theorem le_to_lt_to_lt: ∀n,m,p:nat. n ≤ m → m < p → n < p.
#n #m #p #H (elim H) /3/ qed.

theorem lt_S_to_lt: ∀n,m. S n < m → n < m.
/2/ qed.

theorem ltn_to_ltO: ∀n,m:nat. n < m → 0 < m.
/2/ qed.

theorem lt_O_S : ∀n:nat. O < S n.
/2/ qed.

theorem monotonic_lt_plus_r: 
∀n:nat.monotonic nat lt (λm.n+m).
/2/ qed.

theorem monotonic_lt_plus_l: 
∀n:nat.monotonic nat lt (λm.m+n).
/2/ qed.

theorem lt_plus: ∀n,m,p,q:nat. n < m → p < q → n + p < m + q.
#n #m #p #q #ltnm #ltpq
@(transitive_lt ? (n+q))/2/ qed.

theorem lt_plus_to_lt_l :∀n,p,q:nat. p+n < q+n → p<q.
/2/ qed.

theorem lt_plus_to_lt_r :∀n,p,q:nat. n+p < n+q → p<q.
/2/ qed-.

theorem increasing_to_monotonic: ∀f:nat → nat.
  increasing f → monotonic nat lt f.
#f #incr #n #m #ltnm (elim ltnm) /2/
qed.

theorem monotonic_lt_times_r: 
  ∀c:nat. O < c → monotonic nat lt (λt.(c*t)).
#c #posc #n #m #ltnm
(elim ltnm) normalize
  [/2/ 
  |#a #_ #lt1 @(transitive_le … lt1) //
  ]
qed.

theorem monotonic_lt_times_l: 
  ∀c:nat. 0 < c → monotonic nat lt (λt.(t*c)).
/2/
qed.

theorem lt_to_le_to_lt_times: 
∀n,m,p,q:nat. n < m → p ≤ q → O < q → n*p < m*q.
#n #m #p #q #ltnm #lepq #posq
@(le_to_lt_to_lt ? (n*q))
  [@monotonic_le_times_r //
  |@monotonic_lt_times_l //
  ]
qed.

theorem lt_times:∀n,m,p,q:nat. n<m → p<q → n*p < m*q.
#n #m #p #q #ltnm #ltpq @lt_to_le_to_lt_times/2/
qed.

theorem lt_plus_to_minus_r: ∀a,b,c. a + b < c → a < c - b.
#a #b #c #H @le_plus_to_minus_r //
qed.

lemma lt_plus_Sn_r: ∀a,x,n. a < a + x + (S n).
/2 width=1/ qed.

theorem lt_S_S_to_lt: ∀n,m:nat. S n < S m → n < m.
(* demo *)
/2/ qed-.

(* not le, lt *)

theorem not_le_Sn_O: ∀ n:nat. S n ≰ 0.
#n @nmk #Hlen0 @(lt_to_not_zero ?? Hlen0) qed.

theorem not_le_to_not_le_S_S: ∀ n,m:nat. n ≰ m → S n ≰ S m.
/3/ qed.

theorem not_le_S_S_to_not_le: ∀ n,m:nat. S n ≰ S m → n ≰ m.
/3/ qed.

theorem not_le_Sn_n: ∀n:nat. S n ≰ n.
#n (elim n) /2/ qed.

theorem lt_to_not_le: ∀n,m. n < m → m ≰ n.
#n #m #Hltnm (elim Hltnm) /3/ qed.

theorem not_le_to_lt: ∀n,m. n ≰ m → m < n.
@nat_elim2 #n
 [#abs @False_ind /2/
 |/2/
 |#m #Hind #HnotleSS @le_S_S @Hind /2/ 
 ]
qed.

(* not lt, le *)

theorem not_lt_to_le: ∀n,m:nat. n ≮ m → m ≤ n.
#n #m #H @le_S_S_to_le @not_le_to_lt /2/ qed.

theorem le_to_not_lt: ∀n,m:nat. n ≤ m → m ≮ n.
#n #m #H @lt_to_not_le /2/ (* /3/ *) qed.

(* Compound conclusion ******************************************************)

theorem decidable_eq_nat : ∀n,m:nat.decidable (n=m).
@nat_elim2 #n [ (cases n) /2/ | /3/ | #m #Hind (cases Hind) /3/]
qed. 

theorem decidable_le: ∀n,m. decidable (n≤m).
@nat_elim2 #n /2/ #m * /3/ qed.

theorem decidable_lt: ∀n,m. decidable (n < m).
#n #m @decidable_le  qed.

theorem le_to_or_lt_eq: ∀n,m:nat. n ≤ m → n < m ∨ n = m.
#n #m #lenm (elim lenm) /3/ qed.

theorem eq_or_gt: ∀n. 0 = n ∨ 0 < n.
#n elim (le_to_or_lt_eq 0 n ?) // /2 width=1/
qed-.

theorem increasing_to_le2: ∀f:nat → nat. increasing f → 
  ∀m:nat. f 0 ≤ m → ∃i. f i ≤ m ∧ m < f (S i).
#f #incr #m #lem (elim lem)
  [@(ex_intro ? ? O) /2/
  |#n #len * #a * #len #ltnr (cases(le_to_or_lt_eq … ltnr)) #H
    [@(ex_intro ? ? a) % /2/ 
    |@(ex_intro ? ? (S a)) % //
    ]
  ]
qed.

lemma le_inv_plus_l: ∀x,y,z. x + y ≤ z → x ≤ z - y ∧ y ≤ z.
/3/ qed-.

lemma lt_inv_plus_l: ∀x,y,z. x + y < z → x < z ∧ y < z - x.
/3/ qed-.

lemma lt_or_ge: ∀m,n. m < n ∨ n ≤ m.
#m #n elim (decidable_lt m n) /2/ /3/
qed-.

lemma le_or_ge: ∀m,n. m ≤ n ∨ n ≤ m.
#m #n elim (decidable_le m n) /2/ /4/
qed-.

lemma le_inv_S1: ∀x,y. S x ≤ y → ∃∃z. x ≤ z & y = S z.
#x #y #H elim H -y /2 width=3 by ex2_intro/
#y #_ * #n #Hxn #H destruct /3 width=3 by le_S, ex2_intro/
qed-. 

(* More general conclusion **************************************************)

theorem nat_ind_plus: ∀R:predicate nat.
                      R 0 → (∀n. R n → R (n + 1)) → ∀n. R n.
/3 by nat_ind/ qed-.

theorem lt_O_n_elim: ∀n:nat. 0 < n → 
  ∀P:nat → Prop.(∀m:nat.P (S m)) → P n.
#n (elim n) // #abs @False_ind /2/ @absurd
qed.

theorem le_n_O_elim: ∀n:nat. n ≤ O → ∀P: nat →Prop. P O → P n.
#n (cases n) // #a #abs @False_ind /2/ qed. 

theorem le_n_Sm_elim : ∀n,m:nat.n ≤ S m → 
∀P:Prop. (S n ≤ S m → P) → (n=S m → P) → P.
#n #m #Hle #P (elim Hle) /3/ qed.

theorem nat_elim1 : ∀n:nat.∀P:nat → Prop. 
(∀m.(∀p. p < m → P p) → P m) → P n.
#n #P #H 
cut (∀q:nat. q ≤ n → P q) /2/
(elim n) 
 [#q #HleO (* applica male *) 
    @(le_n_O_elim ? HleO)
    @H #p #ltpO @False_ind /2/ (* 3 *)
 |#p #Hind #q #HleS 
    @H #a #lta @Hind @le_S_S_to_le /2/
 ]
qed.

fact f_ind_aux: ∀A. ∀f:A→ℕ. ∀P:predicate A.
                (∀n. (∀a. f a < n → P a) → ∀a. f a = n → P a) →
                ∀n,a. f a = n → P a.
#A #f #P #H #n @(nat_elim1 … n) -n #n /3 width=3/ (**) (* auto slow (34s) without #n *)
qed-.

lemma f_ind: ∀A. ∀f:A→ℕ. ∀P:predicate A.
             (∀n. (∀a. f a < n → P a) → ∀a. f a = n → P a) → ∀a. P a.
#A #f #P #H #a
@(f_ind_aux … H) -H [2: // | skip ]
qed-.

fact f2_ind_aux: ∀A1,A2. ∀f:A1→A2→ℕ. ∀P:relation2 A1 A2.
                 (∀n. (∀a1,a2. f a1 a2 < n → P a1 a2) → ∀a1,a2. f a1 a2 = n → P a1 a2) →
                 ∀n,a1,a2. f a1 a2 = n → P a1 a2.
#A1 #A2 #f #P #H #n @(nat_elim1 … n) -n #n /3 width=3/ (**) (* auto slow (34s) without #n *)
qed-.

lemma f2_ind: ∀A1,A2. ∀f:A1→A2→ℕ. ∀P:relation2 A1 A2.
              (∀n. (∀a1,a2. f a1 a2 < n → P a1 a2) → ∀a1,a2. f a1 a2 = n → P a1 a2) →
              ∀a1,a2. P a1 a2.
#A1 #A2 #f #P #H #a1 #a2
@(f2_ind_aux … H) -H [2: // | skip ]
qed-. 

fact f3_ind_aux: ∀A1,A2,A3. ∀f:A1→A2→A3→ℕ. ∀P:relation3 A1 A2 A3.
                 (∀n. (∀a1,a2,a3. f a1 a2 a3 < n → P a1 a2 a3) → ∀a1,a2,a3. f a1 a2 a3 = n → P a1 a2 a3) →
                 ∀n,a1,a2,a3. f a1 a2 a3 = n → P a1 a2 a3.
#A1 #A2 #A3 #f #P #H #n @(nat_elim1 … n) -n #n /3 width=3/ (**) (* auto slow (34s) without #n *)
qed-.

lemma f3_ind: ∀A1,A2,A3. ∀f:A1→A2→A3→ℕ. ∀P:relation3 A1 A2 A3.
              (∀n. (∀a1,a2,a3. f a1 a2 a3 < n → P a1 a2 a3) → ∀a1,a2,a3. f a1 a2 a3 = n → P a1 a2 a3) →
              ∀a1,a2,a3. P a1 a2 a3.
#A1 #A2 #A3 #f #P #H #a1 #a2 #a3
@(f3_ind_aux … H) -H [2: // | skip ]
qed-. 

(* More negated equalities **************************************************)

theorem lt_to_not_eq : ∀n,m:nat. n < m → n ≠ m.
#n #m #H @not_to_not /2/ qed.

(* More equalities **********************************************************)

theorem le_n_O_to_eq : ∀n:nat. n ≤ 0 → 0=n.
#n (cases n) // #a  #abs @False_ind /2/ qed.

theorem le_to_le_to_eq: ∀n,m. n ≤ m → m ≤ n → n = m.
@nat_elim2 /4 by le_n_O_to_eq, monotonic_pred, eq_f, sym_eq/
qed. 

theorem increasing_to_injective: ∀f:nat → nat.
  increasing f → injective nat nat f.
#f #incr #n #m cases(decidable_le n m)
  [#lenm cases(le_to_or_lt_eq … lenm) //
   #lenm #eqf @False_ind @(absurd … eqf) @lt_to_not_eq 
   @increasing_to_monotonic //
  |#nlenm #eqf @False_ind @(absurd … eqf) @sym_not_eq 
   @lt_to_not_eq @increasing_to_monotonic /2/
  ]
qed.

theorem minus_Sn_m: ∀m,n:nat. m ≤ n → S n -m = S (n-m).
(* qualcosa da capire qui 
#n #m #lenm nelim lenm napplyS refl_eq. *)
@nat_elim2 
  [//
  |#n #abs @False_ind /2/ 
  |#n #m #Hind #c applyS Hind /2/
  ]
qed.

theorem plus_minus:
∀m,n,p:nat. m ≤ n → (n-m)+p = (n+p)-m.
@nat_elim2 
  [//
  |#n #p #abs @False_ind /2/
  |normalize/3/
  ]
qed.

theorem minus_plus_m_m: ∀n,m:nat.n = (n+m)-m.
/2/ qed.

theorem plus_minus_m_m: ∀n,m:nat.
  m ≤ n → n = (n-m)+m.
#n #m #lemn @sym_eq /2/ qed.

theorem minus_to_plus :∀n,m,p:nat.
  m ≤ n → n-m = p → n = m+p.
#n #m #p #lemn #eqp (applyS plus_minus_m_m) //
qed.

theorem plus_to_minus :∀n,m,p:nat.n = m+p → n-m = p.
#n #m #p #eqp @sym_eq (applyS (minus_plus_m_m p m))
qed.

theorem minus_pred_pred : ∀n,m:nat. O < n → O < m → 
pred n - pred m = n - m.
#n #m #posn #posm @(lt_O_n_elim n posn) @(lt_O_n_elim m posm) //.
qed.

theorem plus_minus_associative: ∀x,y,z. z ≤ y → x + (y - z) = x + y - z.
/2 by plus_minus/ qed.

(* More atomic conclusion ***************************************************)

(* le *)

theorem le_n_fn: ∀f:nat → nat. 
  increasing f → ∀n:nat. n ≤ f n.
#f #incr #n (elim n) /2/
qed-.

theorem monotonic_le_minus_l: 
∀p,q,n:nat. q ≤ p → q-n ≤ p-n.
@nat_elim2 #p #q
  [#lePO @(le_n_O_elim ? lePO) //
  |//
  |#Hind #n (cases n) // #a #leSS @Hind /2/
  ]
qed.

theorem le_minus_to_plus: ∀n,m,p. n-m ≤ p → n≤ p+m.
#n #m #p #lep @transitive_le
  [|@le_plus_minus_m_m | @monotonic_le_plus_l // ]
qed.

theorem le_minus_to_plus_r: ∀a,b,c. c ≤ b → a ≤ b - c → a + c ≤ b.
#a #b #c #Hlecb #H >(plus_minus_m_m … Hlecb) /2/
qed.

theorem le_plus_to_minus: ∀n,m,p. n ≤ p+m → n-m ≤ p.
#n #m #p #lep /2/ qed.

theorem monotonic_le_minus_r: 
∀p,q,n:nat. q ≤ p → n-p ≤ n-q.
#p #q #n #lepq @le_plus_to_minus
@(transitive_le … (le_plus_minus_m_m ? q)) /2/
qed.

theorem increasing_to_le: ∀f:nat → nat. 
  increasing f → ∀m:nat.∃i.m ≤ f i.
#f #incr #m (elim m) /2/#n * #a #lenfa
@(ex_intro ?? (S a)) /2/
qed.

(* thus is le_plus
lemma le_plus_compatible: ∀x1,x2,y1,y2. x1 ≤ y1 → x2 ≤ y2 → x1 + x2 ≤ y1 + y2.
#x1 #y1 #x2 #y2 #H1 #H2 /2/ @le_plus // /2/ /3 by le_minus_to_plus, monotonic_le_plus_r, transitive_le/ qed.
*)

lemma minus_le: ∀x,y. x - y ≤ x.
/2 width=1/ qed.

(* lt *)

theorem not_eq_to_le_to_lt: ∀n,m. n≠m → n≤m → n<m.
#n #m #Hneq #Hle cases (le_to_or_lt_eq ?? Hle) //
#Heq @not_le_to_lt /2/ qed-.

theorem lt_times_n_to_lt_l: 
∀n,p,q:nat. p*n < q*n → p < q.
#n #p #q #Hlt (elim (decidable_lt p q)) //
#nltpq @False_ind @(absurd ? ? (lt_to_not_le ? ? Hlt))
applyS monotonic_le_times_r /2/
qed.

theorem lt_times_n_to_lt_r: 
∀n,p,q:nat. n*p < n*q → p < q.
/2/ qed-.

theorem lt_minus_to_plus: ∀a,b,c. a - b < c → a < c + b.
#a #b #c #H @not_le_to_lt 
@(not_to_not … (lt_to_not_le …H)) /2/
qed.

theorem lt_minus_to_plus_r: ∀a,b,c. a < b - c → a + c < b.
#a #b #c #H @not_le_to_lt @(not_to_not … (le_plus_to_minus …))
@lt_to_not_le //
qed.

theorem lt_plus_to_minus: ∀n,m,p. m ≤ n → n < p+m → n-m < p.
#n #m #p #lenm #H normalize <minus_Sn_m // @le_plus_to_minus //
qed.

theorem monotonic_lt_minus_l: ∀p,q,n. n ≤ q → q < p → q - n < p - n.
#p #q #n #H1 #H2
@lt_plus_to_minus_r <plus_minus_m_m //
qed.

(* More compound conclusion *************************************************)

lemma discr_minus_x_xy: ∀x,y. x = x - y → x = 0 ∨ y = 0.
* /2 width=1/ #x * /2 width=1/ #y normalize #H 
lapply (minus_le x y) <H -H #H
elim (not_le_Sn_n x) #H0 elim (H0 ?) //
qed-.

lemma plus_le_0: ∀x,y. x + y ≤ 0 → x = 0 ∧ y = 0.
#x #y #H elim (le_inv_plus_l … H) -H #H1 #H2 /3 width=1/
qed-.

(* Still more equalities ****************************************************)

theorem eq_minus_O: ∀n,m:nat.
  n ≤ m → n-m = O.
#n #m #lenm @(le_n_O_elim (n-m)) /2/
qed.

theorem distributive_times_minus: distributive ? times minus.
#a #b #c
(cases (decidable_lt b c)) #Hbc
 [> eq_minus_O [2:/2/] >eq_minus_O // 
  @monotonic_le_times_r /2/
 |@sym_eq (applyS plus_to_minus) <distributive_times_plus 
  @eq_f (applyS plus_minus_m_m) /2/
qed.

theorem minus_plus: ∀n,m,p. n-m-p = n -(m+p).
#n #m #p 
cases (decidable_le (m+p) n) #Hlt
  [@plus_to_minus @plus_to_minus <associative_plus
   @minus_to_plus //
  |cut (n ≤ m+p) [@(transitive_le … (le_n_Sn …)) @not_le_to_lt //]
   #H >eq_minus_O /2/ (* >eq_minus_O // *) 
  ]
qed.

theorem minus_minus: ∀n,m,p:nat. p ≤ m → m ≤ n →
  p+(n-m) = n-(m-p).
#n #m #p #lepm #lemn
@sym_eq @plus_to_minus <associative_plus <plus_minus_m_m //
<commutative_plus <plus_minus_m_m //
qed.

lemma minus_minus_associative: ∀x,y,z. z ≤ y → y ≤ x → x - (y - z) = x - y + z.
/2 width=1 by minus_minus/ qed-.

lemma minus_minus_comm: ∀a,b,c. a - b - c = a - c - b.
/3 by monotonic_le_minus_l, le_to_le_to_eq/ qed.

lemma minus_le_minus_minus_comm: ∀b,c,a. c ≤ b → a - (b - c) = a + c - b.
#b #c #a #H >(plus_minus_m_m b c) in ⊢ (? ? ?%); //
qed.

lemma minus_minus_m_m: ∀m,n. n ≤ m → m - (m - n) = n.
/2 width=1/ qed.

lemma minus_plus_plus_l: ∀x,y,h. (x + h) - (y + h) = x - y.
// qed.

lemma plus_minus_plus_plus_l: ∀z,x,y,h. z + (x + h) - (y + h) = z + x - y.
// qed.

lemma minus_plus_minus_l: ∀x,y,z. y ≤ z → (z + x) - (z - y) = x + y.
/2 width=1 by minus_minus_associative/ qed-.

(* Stilll more atomic conclusion ********************************************)

(* le *)

lemma le_fwd_plus_plus_ge: ∀m1,m2. m2 ≤ m1 → ∀n1,n2. m1 + n1 ≤ m2 + n2 → n1 ≤ n2.
#m1 #m2 #H #n1 #n2 >commutative_plus
#H elim (le_inv_plus_l … H) -H >commutative_plus <minus_le_minus_minus_comm //
#H #_ @(transitive_le … H) /2 width=1/
qed-. 

(*********************** boolean arithmetics ********************) 

include "basics/bool.ma".

let rec eqb n m ≝ 
match n with 
  [ O ⇒ match m with [ O ⇒ true | S q ⇒ false] 
  | S p ⇒ match m with [ O ⇒ false | S q ⇒ eqb p q]
  ].

theorem eqb_elim : ∀ n,m:nat.∀ P:bool → Prop.
(n=m → (P true)) → (n ≠ m → (P false)) → (P (eqb n m)). 
@nat_elim2 
  [#n (cases n) normalize /3/ 
  |normalize /3/
  |normalize /4/ 
  ] 
qed.

theorem eqb_n_n: ∀n. eqb n n = true.
#n (elim n) normalize // qed. 

theorem eqb_true_to_eq: ∀n,m:nat. eqb n m = true → n = m.
#n #m @(eqb_elim n m) // #_ #abs @False_ind /2/ qed.

theorem eqb_false_to_not_eq: ∀n,m:nat. eqb n m = false → n ≠ m.
#n #m @(eqb_elim n m) /2/ qed.

theorem eq_to_eqb_true: ∀n,m:nat.n = m → eqb n m = true.
// qed.

theorem not_eq_to_eqb_false: ∀n,m:nat.
  n ≠  m → eqb n m = false.
#n #m #noteq @eqb_elim// #Heq @False_ind /2/ qed.

let rec leb n m ≝ 
match n with 
    [ O ⇒ true
    | (S p) ⇒
	match m with 
        [ O ⇒ false
	      | (S q) ⇒ leb p q]].

theorem leb_elim: ∀n,m:nat. ∀P:bool → Prop. 
(n ≤ m → P true) → (n ≰ m → P false) → P (leb n m).
@nat_elim2 normalize
  [/2/
  |/3/
  |#n #m #Hind #P #Pt #Pf @Hind
    [#lenm @Pt @le_S_S // |#nlenm @Pf /2/ ]
  ]
qed.

theorem leb_true_to_le:∀n,m.leb n m = true → n ≤ m.
#n #m @leb_elim // #_ #abs @False_ind /2/ qed.

theorem leb_false_to_not_le:∀n,m.
  leb n m = false → n ≰ m.
#n #m @leb_elim // #_ #abs @False_ind /2/ qed.

theorem le_to_leb_true: ∀n,m. n ≤ m → leb n m = true.
#n #m @leb_elim // #H #H1 @False_ind /2/ qed.

theorem not_le_to_leb_false: ∀n,m. n ≰ m → leb n m = false.
#n #m @leb_elim // #H #H1 @False_ind /2/ qed.

theorem lt_to_leb_false: ∀n,m. m < n → leb n m = false.
/3/ qed.

(* min e max *)
definition min: nat →nat →nat ≝
λn.λm. if leb n m then n else m.

definition max: nat →nat →nat ≝
λn.λm. if leb n m then m else n.

lemma commutative_min: commutative ? min.
#n #m normalize @leb_elim 
  [@leb_elim normalize /2/
  |#notle >(le_to_leb_true …) // @(transitive_le ? (S m)) /2/
  ] qed.

lemma le_minr: ∀i,n,m. i ≤ min n m → i ≤ m.
#i #n #m normalize @leb_elim normalize /2/ qed. 

lemma le_minl: ∀i,n,m. i ≤ min n m → i ≤ n.
/2/ qed-.

lemma to_min: ∀i,n,m. i ≤ n → i ≤ m → i ≤ min n m.
#i #n #m #lein #leim normalize (cases (leb n m)) 
normalize // qed.

lemma commutative_max: commutative ? max.
#n #m normalize @leb_elim 
  [@leb_elim normalize /2/
  |#notle >(le_to_leb_true …) // @(transitive_le ? (S m)) /2/
  ] qed.

lemma le_maxl: ∀i,n,m. max n m ≤ i → n ≤ i.
#i #n #m normalize @leb_elim normalize /2/ qed. 

lemma le_maxr: ∀i,n,m. max n m ≤ i → m ≤ i.
/2/ qed-.

lemma to_max: ∀i,n,m. n ≤ i → m ≤ i → max n m ≤ i.
#i #n #m #leni #lemi normalize (cases (leb n m)) 
normalize // qed.
