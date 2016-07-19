(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

(* To be ported
include "nat/primes.ma".
include "nat/lt_arith.ma".

(* upper bound by Bertrand's conjecture. *)
(* Too difficult to prove.        
let rec nth_prime n \def
match n with
  [ O \Rightarrow (S(S O))
  | (S p) \Rightarrow
    let previous_prime \def S (nth_prime p) in
    min_aux previous_prime ((S(S O))*previous_prime) primeb].

theorem example8 : nth_prime (S(S O)) = (S(S(S(S(S O))))).
normalize.reflexivity.
qed.

theorem example9 : nth_prime (S(S(S O))) = (S(S(S(S(S(S(S O))))))).
normalize.reflexivity.
qed.

theorem example10 : nth_prime (S(S(S(S O)))) = (S(S(S(S(S(S(S(S(S(S(S O))))))))))).
normalize.reflexivity.
qed. *)

theorem smallest_factor_fact: \forall n:nat.
n < smallest_factor (S n!).
intros.
apply not_le_to_lt.unfold Not.
intro.
apply (not_divides_S_fact n (smallest_factor(S n!))).
apply lt_SO_smallest_factor.
unfold lt.apply le_S_S.apply le_SO_fact.
assumption.
apply divides_smallest_factor_n.
unfold lt.apply le_S_S.apply le_O_n.
qed.

theorem ex_prime: \forall n. (S O) \le n \to \exists m.
n < m \land m \le S n! \land (prime m).
intros.
elim H.
apply (ex_intro nat ? (S(S O))).
split.split.apply (le_n (S(S O))).
apply (le_n (S(S O))).apply (primeb_to_Prop (S(S O))).
apply (ex_intro nat ? (smallest_factor (S (S n1)!))).
split.split.
apply smallest_factor_fact.
apply le_smallest_factor_n.
(* Andrea: ancora hint non lo trova *)
apply prime_smallest_factor_n.unfold lt.
apply le_S.apply le_SSO_fact.
unfold lt.apply le_S_S.assumption.
qed.

let rec nth_prime n \def
match n with
  [ O \Rightarrow (S(S O))
  | (S p) \Rightarrow
    let previous_prime \def (nth_prime p) in
    let upper_bound \def S previous_prime! in
    min_aux upper_bound (S previous_prime) primeb].
    
(* it works
theorem example11 : nth_prime (S(S O)) = (S(S(S(S(S O))))).
normalize.reflexivity.
qed.

theorem example12: nth_prime (S(S(S O))) = (S(S(S(S(S(S(S O))))))).
normalize.reflexivity.
qed.

theorem example13 : nth_prime (S(S(S(S O)))) = (S(S(S(S(S(S(S(S(S(S(S O))))))))))).
normalize.reflexivity.
qed.

alias num (instance 0) = "natural number".
theorem example14 : nth_prime 18 = 67.
normalize.reflexivity.
qed.
*)

theorem prime_nth_prime : \forall n:nat.prime (nth_prime n).
intro.
apply (nat_case n).simplify.
apply (primeb_to_Prop (S(S O))).
intro.
change with
(let previous_prime \def (nth_prime m) in
let upper_bound \def S previous_prime! in
prime (min_aux upper_bound (S previous_prime) primeb)).
apply primeb_true_to_prime.
apply f_min_aux_true.
apply (ex_intro nat ? (smallest_factor (S (nth_prime m)!))).
split.split.
apply smallest_factor_fact.
apply transitive_le;
 [2: apply le_smallest_factor_n
 | skip
 | apply (le_plus_n_r (S (nth_prime m)) (S (fact (nth_prime m))))
 ].
apply prime_to_primeb_true.
apply prime_smallest_factor_n.unfold lt.
apply le_S_S.apply le_SO_fact.
qed.

(* properties of nth_prime *)
theorem increasing_nth_prime: increasing nth_prime.
unfold increasing.
intros.
change with
(let previous_prime \def (nth_prime n) in
let upper_bound \def S previous_prime! in
(S previous_prime) \le min_aux upper_bound (S previous_prime) primeb).
intros.
apply le_min_aux.
qed.

variant lt_nth_prime_n_nth_prime_Sn :\forall n:nat. 
(nth_prime n) < (nth_prime (S n)) \def increasing_nth_prime.

theorem injective_nth_prime: injective nat nat nth_prime.
apply increasing_to_injective.
apply increasing_nth_prime.
qed.

theorem lt_SO_nth_prime_n : \forall n:nat. (S O) \lt nth_prime n.
intros. elim n.unfold lt.apply le_n.
apply (trans_lt ? (nth_prime n1)).
assumption.apply lt_nth_prime_n_nth_prime_Sn.
qed.

theorem lt_O_nth_prime_n : \forall n:nat. O \lt nth_prime n.
intros.apply (trans_lt O (S O)).
unfold lt. apply le_n.apply lt_SO_nth_prime_n.
qed.

theorem lt_n_nth_prime_n : \forall n:nat. n \lt nth_prime n.
intro.
elim n
  [apply lt_O_nth_prime_n
  |apply (lt_to_le_to_lt ? (S (nth_prime n1)))
    [unfold.apply le_S_S.assumption
    |apply lt_nth_prime_n_nth_prime_Sn
    ]
  ]
qed.

theorem ex_m_le_n_nth_prime_m: 
\forall n: nat. nth_prime O \le n \to 
\exists m. nth_prime m \le n \land n < nth_prime (S m).
intros.
apply increasing_to_le2.
exact lt_nth_prime_n_nth_prime_Sn.assumption.
qed.

theorem lt_nth_prime_to_not_prime: \forall n,m. nth_prime n < m \to m < nth_prime (S n) 
\to \lnot (prime m).
intros.
apply primeb_false_to_not_prime.
letin previous_prime \def (nth_prime n).
letin upper_bound \def (S previous_prime!).
apply (lt_min_aux_to_false primeb (S previous_prime) upper_bound m).
assumption.
unfold lt.
apply (transitive_le (S m) (nth_prime (S n)) (min_aux (S (fact (nth_prime n))) (S (nth_prime n)) primeb) ? ?);
  [apply (H1).
  |apply (le_n (min_aux (S (fact (nth_prime n))) (S (nth_prime n)) primeb)).
  ]
qed.

(* nth_prime enumerates all primes *)
theorem prime_to_nth_prime : \forall p:nat. prime p \to
\exists i. nth_prime i = p.
intros.
cut (\exists m. nth_prime m \le p \land p < nth_prime (S m)).
elim Hcut.elim H1.
cut (nth_prime a < p \lor nth_prime a = p).
elim Hcut1.
absurd (prime p).
assumption.
apply (lt_nth_prime_to_not_prime a).assumption.assumption.
apply (ex_intro nat ? a).assumption.
apply le_to_or_lt_eq.assumption.
apply ex_m_le_n_nth_prime_m.
simplify.unfold prime in H.elim H.assumption.
qed.
*)