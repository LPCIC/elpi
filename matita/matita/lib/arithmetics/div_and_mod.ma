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

include "arithmetics/nat.ma".

let rec mod_aux p m n: nat ≝
match p with
  [ O ⇒ m
  | S q ⇒ match (leb m n) with
    [ true ⇒ m
    | false ⇒ mod_aux q (m-(S n)) n]].

definition mod : nat → nat → nat ≝
λn,m. match m with 
  [ O ⇒ n
  | S p ⇒ mod_aux n n p]. 

interpretation "natural remainder" 'module x y = (mod x y).

let rec div_aux p m n : nat ≝
match p with
  [ O ⇒ O
  | S q ⇒ match (leb m n) with
    [ true ⇒ O
    | false ⇒ S (div_aux q (m-(S n)) n)]].

definition div : nat → nat → nat ≝
λn,m.match m with 
  [ O ⇒ S n
  | S p ⇒ div_aux n n p]. 

interpretation "natural divide" 'divide x y = (div x y).

theorem le_mod_aux_m_m: 
∀p,n,m. n ≤ p → mod_aux p n m ≤ m.
#p (elim p)
[ normalize #n #m #lenO @(le_n_O_elim …lenO) //
| #q #Hind #n #m #len normalize 
    @(leb_elim n m) normalize //
    #notlenm @Hind @le_plus_to_minus
    @(transitive_le … len) /2/
qed.

theorem lt_mod_m_m: ∀n,m. O < m → n \mod m  < m.
#n #m (cases m) 
  [#abs @False_ind /2/
  |#p #_ normalize @le_S_S /2/ 
  ]
qed.

theorem div_aux_mod_aux: ∀p,n,m:nat. 
n=(div_aux p n m)*(S m) + (mod_aux p n m).
#p (elim p)
  [#n #m normalize //
  |#q #Hind #n #m normalize
     @(leb_elim n m) #lenm normalize //
     >associative_plus <(Hind (n-(S m)) m)
     applyS plus_minus_m_m (* bello *) /2/
qed.

theorem div_mod: ∀n,m:nat. n=(n / m)*m+(n \mod m).
#n #m (cases m) normalize //
qed.

theorem eq_times_div_minus_mod:
∀a,b:nat. (a / b) * b = a - (a \mod b).
#a #b (applyS minus_plus_m_m) qed.

inductive div_mod_spec (n,m,q,r:nat) : Prop ≝
div_mod_spec_intro: r < m → n=q*m+r → div_mod_spec n m q r.

theorem div_mod_spec_to_not_eq_O: 
  ∀n,m,q,r.div_mod_spec n m q r → m ≠ O.
#n #m #q #r * /2/ 
qed.

theorem div_mod_spec_div_mod: 
  ∀n,m. O < m → div_mod_spec n m (n / m) (n \mod m).
#n #m #posm % /2/ qed.

theorem div_mod_spec_to_eq :∀ a,b,q,r,q1,r1.
div_mod_spec a b q r → div_mod_spec a b q1 r1 → q = q1.
#a #b #q #r #q1 #r1 * #ltrb #spec *  #ltr1b #spec1
@(leb_elim q q1) #leqq1
  [(elim (le_to_or_lt_eq … leqq1)) //
     #ltqq1 @False_ind @(absurd ?? (not_le_Sn_n a))
     @(lt_to_le_to_lt ? ((S q)*b) ?)
      [>spec (applyS (monotonic_lt_plus_r … ltrb))
      |@(transitive_le ? (q1*b)) /2/
      ]
  (* this case is symmetric *)
  |@False_ind @(absurd ?? (not_le_Sn_n a))
     @(lt_to_le_to_lt ? ((S q1)*b) ?)
      [>spec1 (applyS (monotonic_lt_plus_r … ltr1b))
      |cut (q1 < q) [/2/] #ltq1q @(transitive_le ? (q*b)) /2/
      ]
  ]
qed.

theorem div_mod_spec_to_eq2: ∀a,b,q,r,q1,r1.
  div_mod_spec a b q r → div_mod_spec a b q1 r1 → r = r1.
#a #b #q #r #q1 #r1 #spec #spec1
cut (q=q1) [@(div_mod_spec_to_eq … spec spec1)] 
#eqq (elim spec) #_ #eqa (elim spec1) #_ #eqa1 
@(injective_plus_r (q*b)) //
qed.

(* boh
theorem div_mod_spec_times : ∀ n,m:nat.div_mod_spec ((S n)*m) (S n) m O.
intros.constructor 1.
unfold lt.apply le_S_S.apply le_O_n. demodulate. reflexivity.
(*rewrite < plus_n_O.rewrite < sym_times.reflexivity.*)
qed. *)

lemma div_plus_times: ∀m,q,r:nat. r < m → (q*m+r)/ m = q.
#m #q #r #ltrm
@(div_mod_spec_to_eq … (div_mod_spec_div_mod ???)) /2/
qed.

lemma mod_plus_times: ∀m,q,r:nat. r < m → (q*m+r) \mod m = r. 
#m #q #r #ltrm
@(div_mod_spec_to_eq2 … (div_mod_spec_div_mod ???)) /2/
qed.

(* some properties of div and mod *)
theorem div_times: ∀a,b:nat. O < b → a*b/b = a.
#a #b #posb 
@(div_mod_spec_to_eq (a*b) b … O (div_mod_spec_div_mod …))
// @div_mod_spec_intro // qed.

theorem div_n_n: ∀n:nat. O < n → n / n = 1.
/2/ qed.

theorem eq_div_O: ∀n,m. n < m → n / m = O.
#n #m #ltnm 
@(div_mod_spec_to_eq n m (n/m) … n (div_mod_spec_div_mod …))
/2/ qed. 

theorem mod_n_n: ∀n:nat. O < n → n \mod n = O.
#n #posn 
@(div_mod_spec_to_eq2 n n … 1 0 (div_mod_spec_div_mod …))
/2/ qed. 

theorem mod_S: ∀n,m:nat. O < m → S (n \mod m) < m → 
((S n) \mod m) = S (n \mod m).
#n #m #posm #H 
@(div_mod_spec_to_eq2 (S n) m … (n / m) ? (div_mod_spec_div_mod …))
// @div_mod_spec_intro// applyS eq_f // 
qed.

theorem mod_O_n: ∀n:nat.O \mod n = O.
/2/ qed.

theorem lt_to_eq_mod: ∀n,m:nat. n < m → n \mod m = n.
#n #m #ltnm 
@(div_mod_spec_to_eq2 n m (n/m) … O n (div_mod_spec_div_mod …))
/2/ qed. 

(*
theorem mod_1: ∀n:nat. mod n 1 = O.
#n @sym_eq @le_n_O_to_eq
@le_S_S_to_le /2/ qed.

theorem div_1: ∀n:nat. div n 1 = n.
#n @sym_eq napplyS (div_mod n 1) qed. *)

theorem or_div_mod: ∀n,q. O < q →
  ((S (n \mod q)=q) ∧ S n = (S (div n q)) * q ∨
  ((S (n \mod q)<q) ∧ S n = (div n q) * q + S (n\mod q))).
#n #q #posq 
(elim (le_to_or_lt_eq ?? (lt_mod_m_m n q posq))) #H
  [%2 % // applyS eq_f // 
  |%1 % // /demod/ <H in ⊢(? ? ? (? % ?)); @eq_f//
  ]
qed.

(* injectivity *)
theorem injective_times_r: 
  ∀n:nat. O < n → injective nat nat (λm:nat.n*m).
#n #posn #a #b #eqn 
<(div_times a n posn) <(div_times b n posn) // 
qed.

theorem injective_times_l: 
    ∀n:nat. O < n → injective nat nat (λm:nat.m*n).
/2/ qed.

(* n_divides computes the pair (div,mod) 
(* p is just an upper bound, acc is an accumulator *)
let rec n_divides_aux p n m acc \def
  match n \mod m with
  [ O \Rightarrow 
    match p with
      [ O \Rightarrow pair nat nat acc n
      | (S p) \Rightarrow n_divides_aux p (n / m) m (S acc)]
  | (S a) \Rightarrow pair nat nat acc n].

(* n_divides n m = <q,r> if m divides n q times, with remainder r *)
definition n_divides \def \lambda n,m:nat.n_divides_aux n n m O. *)

(* inequalities *)

theorem lt_div_S: ∀n,m. O < m → n < S(n / m)*m.
#n #m #posm (change with (n < m +(n/m)*m))
>(div_mod n m) in ⊢ (? % ?); >commutative_plus 
@monotonic_lt_plus_l @lt_mod_m_m // 
qed.

theorem le_div: ∀n,m. O < n → m/n ≤ m.
#n #m #posn
>(div_mod m n) in ⊢ (? ? %); @(transitive_le ? (m/n*n)) /2/
qed.

theorem le_plus_mod: ∀m,n,q. O < q →
(m+n) \mod q ≤ m \mod q + n \mod q .
#m #n #q #posq
(elim (decidable_le q (m \mod q + n \mod q))) #Hle
  [@(transitive_le … Hle) @le_S_S_to_le @le_S /2/
  |cut ((m+n)\mod q = m\mod q+n\mod q) //
     @(div_mod_spec_to_eq2 … (m/q + n/q) ? (div_mod_spec_div_mod … posq)).
     @div_mod_spec_intro
      [@not_le_to_lt //
      |>(div_mod n q) in ⊢ (? ? (? ? %) ?);
       (applyS (eq_f … (λx.plus x (n \mod q))))
       >(div_mod m q) in ⊢ (? ? (? % ?) ?);
       (applyS (eq_f … (λx.plus x (m \mod q)))) //
      ]
  ]
qed.

theorem le_plus_div: ∀m,n,q. O < q →
  m/q + n/q \le (m+n)/q.
#m #n #q #posq @(le_times_to_le … posq)
@(le_plus_to_le_r ((m+n) \mod q))
(* bruttino *)
>commutative_times in ⊢ (? ? %); <div_mod
>(div_mod m q) in ⊢ (? ? (? % ?)); >(div_mod n q) in ⊢ (? ? (? ? %));
>commutative_plus in ⊢ (? ? (? % ?)); >associative_plus in ⊢ (? ? %);
<associative_plus in ⊢ (? ? (? ? %)); (applyS monotonic_le_plus_l) /2/
qed.

theorem le_times_to_le_div: ∀a,b,c:nat. 
  O < b → b*c ≤ a → c ≤ a/b.
#a #b #c #posb #Hle
@le_S_S_to_le @(lt_times_n_to_lt_l b) @(le_to_lt_to_lt ? a)/2/
qed.

theorem le_times_to_le_div2: ∀m,n,q. O < q → 
  n ≤ m*q → n/q ≤ m.
#m #n #q #posq #Hle
@(le_times_to_le q ? ? posq) @(le_plus_to_le (n \mod q)) /2/
qed.

(* da spostare 
theorem lt_m_nm: ∀n,m. O < m → 1 < n → m < n*m.
/2/ qed. *)
   
theorem lt_times_to_lt_div: ∀m,n,q. n < m*q → n/q < m.
#m #n #q #Hlt
@(lt_times_n_to_lt_l q …) @(lt_plus_to_lt_l (n \mod q)) /2/
qed.

(*
theorem lt_div: ∀n,m. O < m → 1 < n → m/n < m.
#n #m #posm #lt1n
@lt_times_to_lt_div (applyS lt_m_nm) //.
qed. 
  
theorem le_div_plus_S: ∀m,n,q. O < q →
(m+n)/q \le S(m/q + n/q).
#m #n #q #posq
@le_S_S_to_le @lt_times_to_lt_div
@(lt_to_le_to_lt … (lt_plus … (lt_div_S m … posq) (lt_div_S n … posq)))
//
qed. *)

theorem le_div_S_S_div: ∀n,m. O < m → (S n)/m ≤ S (n /m).
#n #m #posm @le_times_to_le_div2 /2/
qed.

theorem le_times_div_div_times: ∀a,n,m.O < m → 
a*(n/m) ≤ a*n/m. 
#a #n #m #posm @le_times_to_le_div /2/
qed.

theorem monotonic_div: ∀n.O < n →
  monotonic nat le (λm.div m n).
#n #posn #a #b #leab @le_times_to_le_div/2/
qed.

theorem pos_div: ∀n,m:nat. O < m → O < n → n \mod m = O → 
  O < n / m.
#n #m #posm #posn #mod0
@(lt_times_n_to_lt_l m)// (* MITICO *)
qed.

(*
theorem lt_div_n_m_n: ∀n,m:nat. 1 < m → O < n → n / m < n.
#n #m #ltm #posn
@(leb_elim 1 (n / m))/2/ (* MITICO *)
qed. *)

theorem eq_div_div_div_times: ∀n,m,q. O < n → O < m →
 q/n/m = q/(n*m).
#n #m #q #posn #posm
@(div_mod_spec_to_eq … (q\mod n+n*(q/n\mod m)) … (div_mod_spec_div_mod …)) /2/
@div_mod_spec_intro // @(lt_to_le_to_lt ? (n*(S (q/n\mod m))))
  [(applyS monotonic_lt_plus_l) /2/
  |@monotonic_le_times_r/2/
  ]
qed.

theorem eq_div_div_div_div: ∀n,m,q. O < n → O < m →
q/n/m = q/m/n.
#n #m #q #posn #posm
@(trans_eq ? ? (q/(n*m)))
  [/2/
  |@sym_eq (applyS eq_div_div_div_times) //
  ]
qed.

(*
theorem SSO_mod: \forall n,m. O < m \to (S(S O))*n/m = (n/m)*(S(S O)) + mod ((S(S O))*n/m) (S(S O)).
intros.
rewrite < (lt_O_to_div_times n (S(S O))) in ⊢ (? ? ? (? (? (? % ?) ?) ?))
  [rewrite > eq_div_div_div_div
    [rewrite > sym_times in ⊢ (? ? ? (? (? (? (? % ?) ?) ?) ?)).
     apply div_mod.
     apply lt_O_S
    |apply lt_O_S
    |assumption
    ]
  |apply lt_O_S
  ]
qed. *)
(* Forall a,b : N. 0 < b \to b * (a/b) <= a < b * (a/b +1) *)
(* The theorem is shown in two different parts: *)
(*
theorem lt_to_div_to_and_le_times_lt_S: \forall a,b,c:nat.
O \lt b \to a/b = c \to (b*c \le a \land a \lt b*(S c)).
intros.
split
[ rewrite < H1.
  rewrite > sym_times.
  rewrite > eq_times_div_minus_mod
  [ apply (le_minus_m a (a \mod b))
  | assumption
  ]
| rewrite < (times_n_Sm b c).
  rewrite < H1.
  rewrite > sym_times.
  rewrite > (div_mod a b) in \vdash (? % ?)
  [ rewrite > (sym_plus b ((a/b)*b)).
    apply lt_plus_r.
    apply lt_mod_m_m.
    assumption
  | assumption
  ]
]
qed. *)

theorem lt_to_le_times_to_lt_S_to_div: ∀a,c,b:nat.
O < b → (b*c) ≤ a → a < (b*(S c)) → a/b = c.
#a #c #b #posb#lea #lta
@(div_mod_spec_to_eq … (a-b*c) (div_mod_spec_div_mod … posb …))
@div_mod_spec_intro [@lt_plus_to_minus // |/2/]
qed.

theorem div_times_times: ∀a,b,c:nat. O < c → O < b → 
  (a/b) = (a*c)/(b*c).
#a #b #c #posc #posb
>(commutative_times b) <eq_div_div_div_times //
>div_times //
qed.

theorem times_mod: ∀a,b,c:nat.
O < c → O < b → (a*c) \mod (b*c) = c*(a\mod b).
#a #b #c #posc #posb
@(div_mod_spec_to_eq2 (a*c) (b*c) (a/b) ((a*c) \mod (b*c)) (a/b) (c*(a \mod b)))
  [>(div_times_times … posc) // @div_mod_spec_div_mod /2/
  |@div_mod_spec_intro
    [applyS (monotonic_lt_times_r … c posc) /2/
    |(applyS (eq_f …(λx.x*c))) //
    ]
  ]
qed.

theorem le_div_times_m: ∀a,i,m. O < i → O < m →
 (a * (m / i)) / m ≤ a / i.
#a #i #m #posi #posm
@(transitive_le ? ((a*m/i)/m))
  [@monotonic_div /2/
  |>eq_div_div_div_div // >div_times //
  ]
qed.

(* serve ?
theorem le_div_times_Sm: ∀a,i,m. O < i → O < m →
a / i ≤ (a * S (m / i))/m.
intros.
apply (trans_le ? ((a * S (m/i))/((S (m/i))*i)))
  [rewrite < (eq_div_div_div_times ? i)
    [rewrite > lt_O_to_div_times
      [apply le_n
      |apply lt_O_S
      ]
    |apply lt_O_S
    |assumption
    ]
  |apply le_times_to_le_div
    [assumption
    |apply (trans_le ? (m*(a*S (m/i))/(S (m/i)*i)))
      [apply le_times_div_div_times.
       rewrite > (times_n_O O).
       apply lt_times
        [apply lt_O_S
        |assumption
        ]
      |rewrite > sym_times.
       apply le_times_to_le_div2
        [rewrite > (times_n_O O).
         apply lt_times
          [apply lt_O_S
          |assumption
          ]
        |apply le_times_r.
         apply lt_to_le.
         apply lt_div_S.
         assumption
        ]
      ]
    ]
  ]
qed. *)
