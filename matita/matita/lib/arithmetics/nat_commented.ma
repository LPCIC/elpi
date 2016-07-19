(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(*
theorem inj_S : \forall n,m:nat.(S n)=(S m) \to n=m.
//. qed.

theorem plus_Sn_m: ∀n,m:nat. S (n + m) = S n + m.
// qed.

theorem plus_Sn_m1: ∀n,m:nat. S m + n = n + S m.
#n (elim n) normalize // qed.


(* deleterio? *)
theorem plus_n_1 : ∀n:nat. S n = n+1.
// qed.

theorem inj_plus_r: \forall p,n,m:nat. p+n = p+m \to n=m
\def injective_plus_r. 

theorem injective_plus_l: ∀m:nat.injective nat nat (λn.n+m).
/2/ qed.

theorem inj_plus_l: \forall p,n,m:nat. n+p = m+p \to n=m
\def injective_plus_l.

variant sym_times : \forall n,m:nat. n*m = m*n \def
symmetric_times.

theorem times_O_to_O: ∀n,m:nat.n*m=O → n=O ∨ m=O.
napply nat_elim2 /2/ 
#n #m #H normalize #H1 napply False_ind napply not_eq_O_S
// qed.
  
theorem times_n_SO : ∀n:nat. n = n * S O.
#n // qed.

theorem times_SSO_n : ∀n:nat. n + n = (S(S O)) * n.
normalize // qed.

nlemma times_SSO: \forall n.(S(S O))*(S n) = S(S((S(S O))*n)).
// qed.

theorem or_eq_eq_S: \forall n.\exists m. 
n = (S(S O))*m \lor n = S ((S(S O))*m).
#n (elim n)
  ##[@ /2/
  ##|#a #H nelim H #b#ornelim or#aeq
    ##[@ b @ 2 //
    ##|@ (S b) @ 1 /2/
    ##]
qed.

lemma eq_lt: ∀n,m. (n < m) = (S n ≤ m).
// qed. 

theorem trans_le: \forall n,m,p:nat. n \leq m \to m \leq p \to n \leq p
\def transitive_le.

theorem trans_lt: \forall n,m,p:nat. lt n m \to lt m p \to lt n p
\def transitive_lt.

(* this are instances of the le versions *)
theorem lt_S_S_to_lt: ∀n,m. S n < S m → n < m.
/2/ qed. 

theorem lt_to_lt_S_S: ∀n,m. n < m → S n < S m.
/2/ qed. 

(* this is le_S_S_to_le *)
theorem lt_S_to_le: ∀n,m:nat. n < S m → n ≤ m.
/2/ qed.

theorem lt_SO_n_to_lt_O_pred_n: \forall n:nat.
(S O) \lt n \to O \lt (pred n).
intros.
apply (ltn_to_ltO (pred (S O)) (pred n) ?).
 apply (lt_pred (S O) n)
 [ apply (lt_O_S O) 
 | assumption
 ]
qed.

theorem lt_pred: \forall n,m. 
  O < n \to n < m \to pred n < pred m. 
apply nat_elim2
  [intros.apply False_ind.apply (not_le_Sn_O ? H)
  |intros.apply False_ind.apply (not_le_Sn_O ? H1)
  |intros.simplify.unfold.apply le_S_S_to_le.assumption
  ]
qed.

theorem le_pred_to_le:
 ∀n,m. O < m → pred n ≤ pred m → n ≤ m.
intros 2
elim n
[ apply le_O_n
| simplify in H2
  rewrite > (S_pred m)
  [ apply le_S_S
    assumption
  | assumption
  ]
].
qed.
 
theorem eq_to_not_lt: ∀a,b:nat. a = b → a ≮ b.
intros.
unfold Not.
intros.
rewrite > H in H1.
apply (lt_to_not_eq b b)
[ assumption
| reflexivity
]
qed. 

theorem lt_n_m_to_not_lt_m_Sn: ∀n,m. n < m → m ≮ S n.
intros
unfold Not
intro
unfold lt in H
unfold lt in H1
generalize in match (le_S_S ? ? H)
intro
generalize in match (transitive_le ? ? ? H2 H1)
intro
apply (not_le_Sn_n ? H3).
qed. 

(* other abstract properties *)
theorem antisymmetric_le : antisymmetric nat le.
unfold antisymmetric.intros 2.
apply (nat_elim2 (\lambda n,m.(n \leq m \to m \leq n \to n=m))).
intros.apply le_n_O_to_eq.assumption.
intros.apply False_ind.apply (not_le_Sn_O ? H).
intros.apply eq_f.apply H.
apply le_S_S_to_le.assumption.
apply le_S_S_to_le.assumption.
qed.

theorem antisym_le: \forall n,m:nat. n \leq m \to m \leq n \to n=m
\def antisymmetric_le.

theorem le_n_m_to_lt_m_Sn_to_eq_n_m: ∀n,m. n ≤ m → m < S n → n=m.
intros
unfold lt in H1
generalize in match (le_S_S_to_le ? ? H1)
intro
apply antisym_le
assumption.
qed.

theorem le_plus_r: ∀p,n,m:nat. n ≤ m → p + n ≤ p + m
≝ monotonic_le_plus_r.

theorem le_plus_l: \forall p,n,m:nat. n \le m \to n + p \le m + p
\def monotonic_le_plus_l.

variant lt_plus_r: \forall n,p,q:nat. p < q \to n + p < n + q \def
monotonic_lt_plus_r.

variant lt_plus_l: \forall n,p,q:nat. p < q \to p + n < q + n \def
monotonic_lt_plus_l.

theorem le_to_lt_to_lt_plus: ∀a,b,c,d:nat.
a ≤ c → b < d → a + b < c+d.
(* bello /2/ un po' lento *)
#a #b #c #d #leac #lebd 
normalize napplyS le_plus // qed.

theorem le_times_r: \forall p,n,m:nat. n \le m \to p*n \le p*m
\def monotonic_le_times_r. 

theorem monotonic_le_times_l: 
∀m:nat.monotonic nat le (λn.n*m).
/2/ qed.

theorem le_times_l: \forall p,n,m:nat. n \le m \to n*p \le m*p
\def monotonic_le_times_l. 

theorem le_S_times_2: ∀n,m.O < m → n ≤ m → S n ≤ 2*m.
#n #m #posm #lenm  (* interessante *)
applyS (le_plus n m) // qed.

theorem lt_O_times_S_S: ∀n,m:nat.O < (S n)*(S m).
intros.simplify.unfold lt.apply le_S_S.apply le_O_n.
qed.

theorem lt_times_eq_O: \forall a,b:nat.
O < a → a * b = O → b = O.
intros.
apply (nat_case1 b)
[ intros.
  reflexivity
| intros.
  rewrite > H2 in H1.
  rewrite > (S_pred a) in H1
  [ apply False_ind.
    apply (eq_to_not_lt O ((S (pred a))*(S m)))
    [ apply sym_eq.
      assumption
    | apply lt_O_times_S_S
    ]
  | assumption
  ]
]
qed. 

theorem O_lt_times_to_O_lt: \forall a,c:nat.
O \lt (a * c) \to O \lt a.
intros.
apply (nat_case1 a)
[ intros.
  rewrite > H1 in H.
  simplify in H.
  assumption
| intros.
  apply lt_O_S
]
qed.

lemma lt_times_to_lt_O: \forall i,n,m:nat. i < n*m \to O < m.
intros.
elim (le_to_or_lt_eq O ? (le_O_n m))
  [assumption
  |apply False_ind.
   rewrite < H1 in H.
   rewrite < times_n_O in H.
   apply (not_le_Sn_O ? H)
  ]
qed.

theorem monotonic_lt_times_r: 
∀n:nat.monotonic nat lt (λm.(S n)*m).
/2/ 
simplify.
intros.elim n.
simplify.rewrite < plus_n_O.rewrite < plus_n_O.assumption.
apply lt_plus.assumption.assumption.
qed. 

theorem nat_compare_times_l : \forall n,p,q:nat. 
nat_compare p q = nat_compare ((S n) * p) ((S n) * q).
intros.apply nat_compare_elim.intro.
apply nat_compare_elim.
intro.reflexivity.
intro.absurd (p=q).
apply (inj_times_r n).assumption.
apply lt_to_not_eq. assumption.
intro.absurd (q<p).
apply (lt_times_to_lt_r n).assumption.
apply le_to_not_lt.apply lt_to_le.assumption.
intro.rewrite < H.rewrite > nat_compare_n_n.reflexivity.
intro.apply nat_compare_elim.intro.
absurd (p<q).
apply (lt_times_to_lt_r n).assumption.
apply le_to_not_lt.apply lt_to_le.assumption.
intro.absurd (q=p).
symmetry.
apply (inj_times_r n).assumption.
apply lt_to_not_eq.assumption.
intro.reflexivity.
qed.
 
theorem lt_times_plus_times: \forall a,b,n,m:nat. 
a < n \to b < m \to a*m + b < n*m.
intros 3.
apply (nat_case n)
  [intros.apply False_ind.apply (not_le_Sn_O ? H)
  |intros.simplify.
   rewrite < sym_plus.
   unfold.
   change with (S b+a*m1 \leq m1+m*m1).
   apply le_plus
    [assumption
    |apply le_times
      [apply le_S_S_to_le.assumption
      |apply le_n
      ]
    ]
  ]
qed.

theorem not_eq_to_le_to_le_minus: 
  ∀n,m.n ≠ m → n ≤ m → n ≤ m - 1.
#n * #m (cases m// #m normalize
#H #H1 napply le_S_S_to_le
napplyS (not_eq_to_le_to_lt n (S m) H H1)
qed.

theorem le_SO_minus: \forall n,m:nat.S n \leq m \to S O \leq m-n.
intros.elim H.elim (minus_Sn_n n).apply le_n.
rewrite > minus_Sn_m.
apply le_S.assumption.
apply lt_to_le.assumption.
qed.

theorem minus_le_S_minus_S: \forall n,m:nat. m-n \leq S (m-(S n)).
intros.
apply (nat_elim2 (\lambda n,m.m-n \leq S (m-(S n)))).
intro.elim n1.simplify.apply le_n_Sn.
simplify.rewrite < minus_n_O.apply le_n.
intros.simplify.apply le_n_Sn.
intros.simplify.apply H.
qed.

theorem lt_minus_S_n_to_le_minus_n : \forall n,m,p:nat. m-(S n) < p \to m-n \leq p. 
intros 3.intro.
(* autobatch *)
(* end auto($Revision: 9739 $) proof: TIME=1.33 SIZE=100 DEPTH=100 *)
apply (trans_le (m-n) (S (m-(S n))) p).
apply minus_le_S_minus_S.
assumption.
qed.

theorem le_minus_m: \forall n,m:nat. n-m \leq n.
intros.apply (nat_elim2 (\lambda m,n. n-m \leq n)).
intros.rewrite < minus_n_O.apply le_n.
intros.simplify.apply le_n.
intros.simplify.apply le_S.assumption.
qed.

theorem lt_minus_m: \forall n,m:nat. O < n \to O < m \to n-m \lt n.
intros.apply (lt_O_n_elim n H).intro.
apply (lt_O_n_elim m H1).intro.
simplify.unfold lt.apply le_S_S.apply le_minus_m.
qed.

theorem minus_le_O_to_le: \forall n,m:nat. n-m \leq O \to n \leq m.
intros 2.
apply (nat_elim2 (\lambda n,m:nat.n-m \leq O \to n \leq m)).
intros.apply le_O_n.
simplify.intros. assumption.
simplify.intros.apply le_S_S.apply H.assumption.
qed.

theorem plus_minus: ∀n,m,p. p ≤ m → (n+m)-p = n +(m-p).
#n #m #p #lepm @plus_to_minus >(commutative_plus p)
>associative_plus <plus_minus_m_m //
qed.  

(* serve anche ltb? *)
ndefinition ltb ≝λn,m. leb (S n) m.

theorem ltb_elim: ∀n,m:nat. ∀P:bool → Prop. 
(n < m → P true) → (n ≮ m → P false) → P (ltb n m).
#n #m #P #Hlt #Hnlt
napply leb_elim /3/ qed.

theorem ltb_true_to_lt:∀n,m.ltb n m = true → n < m.
#n #m #Hltb napply leb_true_to_le nassumption
qed.

theorem ltb_false_to_not_lt:∀n,m.
  ltb n m = false → n ≮ m.
#n #m #Hltb napply leb_false_to_not_le nassumption
qed.

theorem lt_to_ltb_true: ∀n,m. n < m → ltb n m = true.
#n #m #Hltb napply le_to_leb_true nassumption
qed.

theorem le_to_ltb_false: ∀n,m. m \le n → ltb n m = false.
#n #m #Hltb napply lt_to_leb_false /2/
qed.

*)
