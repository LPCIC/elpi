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

include "formal_topology/categories.ma".
(*
inductive bool : Type[0] := true : bool | false : bool.

lemma BOOL : objs1 SET.
constructor 1; [apply bool] constructor 1;
[ intros (x y); apply (match x with [ true ⇒ match y with [ true ⇒ True | _ ⇒ False] | false ⇒ match y with [ true ⇒ False | false ⇒ True ]]);
| whd; simplify; intros; cases x; apply I;
| whd; simplify; intros 2; cases x; cases y; simplify; intros; assumption;
| whd; simplify; intros 3; cases x; cases y; cases z; simplify; intros; 
  try assumption; apply I]
qed.

lemma IF_THEN_ELSE_p :
  ∀S:setoid1.∀a,b:S.∀x,y:BOOL.x = y → 
    (λm.match m with [ true ⇒ a | false ⇒ b ]) x =
    (λm.match m with [ true ⇒ a | false ⇒ b ]) y.
whd in ⊢ (?→?→?→%→?);
intros; cases x in e; cases y; simplify; intros; try apply refl1; whd in e; cases e;
qed.

interpretation "unary morphism comprehension with no proof" 'comprehension T P = 
  (mk_unary_morphism T ? P ?).
interpretation "unary morphism1 comprehension with no proof" 'comprehension T P = 
  (mk_unary_morphism1 T ? P ?).

notation > "hvbox({ ident i ∈ s | term 19 p | by })" with precedence 90
for @{ 'comprehension_by $s (λ${ident i}. $p) $by}.
notation < "hvbox({ ident i ∈ s | term 19 p })" with precedence 90
for @{ 'comprehension_by $s (λ${ident i}:$_. $p) $by}.

interpretation "unary morphism comprehension with proof" 'comprehension_by s \eta.f p = 
  (mk_unary_morphism s ? f p).
interpretation "unary morphism1 comprehension with proof" 'comprehension_by s \eta.f p = 
  (mk_unary_morphism1 s ? f p).

(* per il set-indexing vedere capitolo BPTools (foundational tools), Sect. 0.3.4 complete
   lattices, Definizione 0.9 *)
(* USARE L'ESISTENZIALE DEBOLE *)

definition if_then_else ≝ λT:Type.λe,t,f.match e return λ_.T with [ true ⇒ t | false ⇒ f].
notation > "'If' term 19 e 'then' term 19 t 'else' term 90 f" non associative with precedence 19 for @{ 'if_then_else $e $t $f }.
notation < "'If' \nbsp term 19 e \nbsp 'then' \nbsp term 19 t \nbsp 'else' \nbsp term 90 f \nbsp" non associative with precedence 19 for @{ 'if_then_else $e $t $f }.
interpretation "Formula if_then_else" 'if_then_else e t f = (if_then_else ? e t f).

notation > "hvbox(a break ≤ b)" non associative with precedence 45 for @{oa_leq $a $b}.
notation > "a >< b" non associative with precedence 45 for @{oa_overlap $a $b}.
notation > "⋁ p" non associative with precedence 45 for @{oa_join ? $p}.
notation > "⋀ p" non associative with precedence 45 for @{oa_meet ? $p}.
notation > "𝟙" non associative with precedence 90 for @{oa_one}. 
notation > "𝟘" non associative with precedence 90 for @{oa_zero}. 
record OAlgebra : Type[2] := {
  oa_P :> SET1;
  oa_leq : oa_P × oa_P ⇒_1 CPROP;
  oa_overlap: oa_P × oa_P ⇒_1 CPROP;
  oa_meet: ∀I:SET.(I ⇒_2 oa_P) ⇒_2. oa_P;
  oa_join: ∀I:SET.(I ⇒_2 oa_P) ⇒_2. oa_P;
  oa_one: oa_P;
  oa_zero: oa_P;
  oa_leq_refl: ∀a:oa_P. a ≤ a; 
  oa_leq_antisym: ∀a,b:oa_P.a ≤ b → b ≤ a → a = b;
  oa_leq_trans: ∀a,b,c:oa_P.a ≤ b → b ≤ c → a ≤ c;
  oa_overlap_sym: ∀a,b:oa_P.a >< b → b >< a;
  oa_meet_inf: ∀I:SET.∀p_i:I ⇒_2 oa_P.∀p:oa_P.p ≤ (⋀ p_i) = (∀i:I.p ≤ (p_i i));
  oa_join_sup: ∀I:SET.∀p_i:I ⇒_2 oa_P.∀p:oa_P.(⋁ p_i) ≤ p = (∀i:I.p_i i ≤ p);
  oa_zero_bot: ∀p:oa_P.𝟘 ≤ p;
  oa_one_top: ∀p:oa_P.p ≤ 𝟙;
  oa_overlap_preserves_meet_: ∀p,q:oa_P.p >< q → 
        p >< (⋀ { x ∈ BOOL | If x then p else q | IF_THEN_ELSE_p oa_P p q });
  oa_join_split: ∀I:SET.∀p.∀q:I ⇒_2 oa_P.p >< (⋁ q) = (∃i:I.p >< (q i));
  (*oa_base : setoid;
  1) enum non e' il nome giusto perche' non e' suriettiva
  2) manca (vedere altro capitolo) la "suriettivita'" come immagine di insiemi di oa_base
  oa_enum : ums oa_base oa_P;
  oa_density: ∀p,q.(∀i.oa_overlap p (oa_enum i) → oa_overlap q (oa_enum i)) → oa_leq p q
  *)
  oa_density: ∀p,q.(∀r.p >< r → q >< r) → p ≤ q
}.

notation "hvbox(a break ≤ b)" non associative with precedence 45 for @{ 'leq $a $b }.

interpretation "o-algebra leq" 'leq a b = (fun21 ??? (oa_leq ?) a b).

notation "hovbox(a mpadded width -150% (>)< b)" non associative with precedence 45
for @{ 'overlap $a $b}.
interpretation "o-algebra overlap" 'overlap a b = (fun21 ??? (oa_overlap ?) a b).

notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∧) \below (\emsp) \nbsp term 90 p)" 
non associative with precedence 55 for @{ 'oa_meet $p }.
notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∧) \below (ident i ∈  I) break term 90 p)" 
non associative with precedence 55 for @{ 'oa_meet_mk (λ${ident i}:$I.$p) }.

notation > "hovbox(∧ f)" non associative with precedence 65
for @{ 'oa_meet $f }.
interpretation "o-algebra meet" 'oa_meet f = 
  (fun12 ?? (oa_meet ??) f).
interpretation "o-algebra meet with explicit function" 'oa_meet_mk f = 
  (fun12 ?? (oa_meet ??) (mk_unary_morphism1 ?? f ?)).

notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∨) \below (\emsp) \nbsp term 90 p)" 
non associative with precedence 55 for @{ 'oa_join $p }.
notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∨) \below (ident i ∈  I) break term 90 p)" 
non associative with precedence 55 for @{ 'oa_join_mk (λ${ident i}:$I.$p) }.

notation > "hovbox(∨ f)" non associative with precedence 65
for @{ 'oa_join $f }.
interpretation "o-algebra join" 'oa_join f = 
  (fun12 ?? (oa_join ??) f).
interpretation "o-algebra join with explicit function" 'oa_join_mk f = 
  (fun12 ?? (oa_join ??) (mk_unary_morphism ?? f ?)).

definition binary_meet : ∀O:OAlgebra. O × O ⇒_1 O.
intros; split;
[ intros (p q); 
  apply (∧ { x ∈ BOOL | match x with [ true ⇒ p | false ⇒ q ] | IF_THEN_ELSE_p ? p q });
| intros; lapply (prop12 ? O (oa_meet O BOOL));
   [2: apply ({ x ∈ BOOL | match x with [ true ⇒ a | false ⇒ b ] | IF_THEN_ELSE_p ? a b });
   |3: apply ({ x ∈ BOOL | match x with [ true ⇒ a' | false ⇒ b' ] | IF_THEN_ELSE_p ? a' b' });
   | apply Hletin;]
  intro x; simplify; cases x; simplify; assumption;]
qed.

interpretation "o-algebra binary meet" 'and a b = 
  (fun21 ??? (binary_meet ?) a b).

prefer coercion Type[1]_OF_OAlgebra.

definition binary_join : ∀O:OAlgebra. O × O ⇒_1 O.
intros; split;
[ intros (p q); 
  apply (∨ { x ∈ BOOL | match x with [ true ⇒ p | false ⇒ q ] | IF_THEN_ELSE_p ? p q });
| intros; lapply (prop12 ? O (oa_join O BOOL));
   [2: apply ({ x ∈ BOOL | match x with [ true ⇒ a | false ⇒ b ] | IF_THEN_ELSE_p ? a b });
   |3: apply ({ x ∈ BOOL | match x with [ true ⇒ a' | false ⇒ b' ] | IF_THEN_ELSE_p ? a' b' });
   | apply Hletin;]
  intro x; simplify; cases x; simplify; assumption;]
qed.

interpretation "o-algebra binary join" 'or a b = 
  (fun21 ??? (binary_join ?) a b).

lemma oa_overlap_preservers_meet: ∀O:OAlgebra.∀p,q:O.p >< q → p >< (p ∧ q).
intros;  lapply (oa_overlap_preserves_meet_ O p q f) as H; clear f;
(** screenshot "screenoa". *)
assumption;
qed.

notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∨) \below (\emsp) \nbsp term 90 p)" 
non associative with precedence 49 for @{ 'oa_join $p }.
notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (∨) \below (ident i ∈  I) break term 90 p)" 
non associative with precedence 49 for @{ 'oa_join_mk (λ${ident i}:$I.$p) }.
notation < "hovbox(a ∨ b)" left associative with precedence 49
for @{ 'oa_join_mk (λ${ident i}:$_.match $i with [ true ⇒ $a | false ⇒ $b ]) }.

notation > "hovbox(∨ f)" non associative with precedence 64
for @{ 'oa_join $f }.
notation > "hovbox(a ∨ b)" left associative with precedence 49
for @{ 'oa_join (mk_unary_morphism BOOL ? (λx__:bool.match x__ with [ true ⇒ $a | false ⇒ $b ]) (IF_THEN_ELSE_p ? $a $b)) }.

interpretation "o-algebra join" 'oa_join f = 
  (fun12 ?? (oa_join ??) f).
interpretation "o-algebra join with explicit function" 'oa_join_mk f = 
  (fun12 ?? (oa_join ??) (mk_unary_morphism ?? f ?)).

record ORelation (P,Q : OAlgebra) : Type[2] ≝ {
  or_f_ : P ⇒_2 Q;
  or_f_minus_star_ : P ⇒_2 Q;
  or_f_star_ : Q ⇒_2 P;
  or_f_minus_ : Q ⇒_2 P;
  or_prop1_ : ∀p,q. (or_f_ p ≤ q) = (p ≤ or_f_star_ q);
  or_prop2_ : ∀p,q. (or_f_minus_ p ≤ q) = (p ≤ or_f_minus_star_ q);
  or_prop3_ : ∀p,q. (or_f_ p >< q) = (p >< or_f_minus_ q)
}.

definition ORelation_setoid : OAlgebra → OAlgebra → setoid2.
intros (P Q);
constructor 1;
[ apply (ORelation P Q);
| constructor 1;
   (* tenere solo una uguaglianza e usare la proposizione 9.9 per
      le altre (unicita' degli aggiunti e del simmetrico) *)
   [ apply (λp,q. And42 
             (or_f_minus_star_ ?? p = or_f_minus_star_ ?? q) 
             (or_f_minus_ ?? p = or_f_minus_ ?? q) 
             (or_f_ ?? p = or_f_ ?? q) 
             (or_f_star_ ?? p = or_f_star_ ?? q)); 
   | whd; simplify; intros; repeat split; intros; apply refl2;
   | whd; simplify; intros; cases a; clear a; split; 
     intro a; apply sym1; generalize in match a;assumption;
   | whd; simplify; intros; cases a; cases a1; clear a a1; split; intro a;
     [ apply (.= (e a)); apply e4;
     | apply (.= (e1 a)); apply e5;
     | apply (.= (e2 a)); apply e6;
     | apply (.= (e3 a)); apply e7;]]]
qed.

definition ORelation_of_ORelation_setoid : 
  ∀P,Q.ORelation_setoid P Q → ORelation P Q ≝ λP,Q,x.x.
coercion ORelation_of_ORelation_setoid.

definition or_f_minus_star: ∀P,Q:OAlgebra.(ORelation_setoid P Q) ⇒_2 (P ⇒_2 Q).
 intros; constructor 1;
  [ apply or_f_minus_star_;
  | intros; cases e; assumption]
qed.

definition or_f: ∀P,Q:OAlgebra.(ORelation_setoid P Q) ⇒_2 (P ⇒_2 Q).
 intros; constructor 1;
  [ apply or_f_;
  | intros; cases e; assumption]
qed.

definition or_f_minus: ∀P,Q:OAlgebra.(ORelation_setoid P Q) ⇒_2 (Q ⇒_2 P).
 intros; constructor 1;
  [ apply or_f_minus_;
  | intros; cases e; assumption]
qed.

definition or_f_star: ∀P,Q:OAlgebra.(ORelation_setoid P Q) ⇒_2 (Q ⇒_2 P).
 intros; constructor 1;
  [ apply or_f_star_;
  | intros; cases e; assumption]
qed.

lemma arrows1_of_ORelation_setoid : ∀P,Q. ORelation_setoid P Q → (P ⇒_2 Q). 
intros; apply (or_f ?? c);
qed.
coercion arrows1_of_ORelation_setoid.

interpretation "o-relation f⎻*" 'OR_f_minus_star r = (fun12 ?? (or_f_minus_star ? ?) r).
interpretation "o-relation f⎻" 'OR_f_minus r = (fun12 ?? (or_f_minus ? ?) r).
interpretation "o-relation f*" 'OR_f_star r = (fun12 ?? (or_f_star ? ?) r).

definition or_prop1 : ∀P,Q:OAlgebra.∀F:ORelation_setoid P Q.∀p,q.
   (F p ≤ q) =_1 (p ≤ F* q).
intros; apply (or_prop1_ ?? F p q);
qed.

definition or_prop2 : ∀P,Q:OAlgebra.∀F:ORelation_setoid P Q.∀p,q.
   (F⎻ p ≤ q) = (p ≤ F⎻* q).
intros; apply (or_prop2_ ?? F p q);
qed.

definition or_prop3 : ∀P,Q:OAlgebra.∀F:ORelation_setoid P Q.∀p,q.
   (F p >< q) = (p >< F⎻ q).
intros; apply (or_prop3_ ?? F p q);
qed.

definition ORelation_composition : ∀P,Q,R. 
  (ORelation_setoid P Q) × (ORelation_setoid Q R) ⇒_2 (ORelation_setoid P R).
intros;
constructor 1;
[ intros (F G);
  constructor 1;
  [ apply (G ∘ F);
  | apply rule (G⎻* ∘ F⎻* );
  | apply (F* ∘ G* );
  | apply (F⎻ ∘ G⎻);
  | intros; 
    change with ((G (F p) ≤ q) = (p ≤ (F* (G* q))));
    apply (.= (or_prop1 :?));
    apply (or_prop1 :?);
  | intros;
    change with ((F⎻ (G⎻ p) ≤ q) = (p ≤ (G⎻* (F⎻* q))));
    apply (.= (or_prop2 :?));
    apply or_prop2 ; 
  | intros; change with ((G (F (p)) >< q) = (p >< (F⎻ (G⎻ q))));
    apply (.= (or_prop3 :?));
    apply or_prop3;
  ]
| intros; split; simplify; 
   [3: unfold arrows1_of_ORelation_setoid; apply ((†e)‡(†e1));
   |1: apply ((†e)‡(†e1));
   |2,4: apply ((†e1)‡(†e));]]
qed.

definition OA : category2.
split;
[ apply (OAlgebra);
| intros; apply (ORelation_setoid o o1);
| intro O; split;
  [1,2,3,4: apply id2;
  |5,6,7:intros; apply refl1;] 
| apply ORelation_composition;
| intros (P Q R S F G H); split;
   [ change with (H⎻* ∘ G⎻* ∘ F⎻* = H⎻* ∘ (G⎻* ∘ F⎻* ));
     apply (comp_assoc2 ????? (F⎻* ) (G⎻* ) (H⎻* ));
   | apply ((comp_assoc2 ????? (H⎻) (G⎻) (F⎻))^-1);
   | apply ((comp_assoc2 ????? F G H)^-1);
   | apply ((comp_assoc2 ????? H* G* F* ));]
| intros; split; unfold ORelation_composition; simplify; apply id_neutral_left2;
| intros; split; unfold ORelation_composition; simplify; apply id_neutral_right2;]
qed.

definition OAlgebra_of_objs2_OA: objs2 OA → OAlgebra ≝ λx.x.
coercion OAlgebra_of_objs2_OA.

definition ORelation_setoid_of_arrows2_OA: 
  ∀P,Q. arrows2 OA P Q → ORelation_setoid P Q ≝ λP,Q,c.c.
coercion ORelation_setoid_of_arrows2_OA.

prefer coercion Type_OF_objs2.

notation > "B ⇒_\o2 C" right associative with precedence 72 for @{'arrows2_OA $B $C}.
notation "B ⇒\sub (\o 2) C" right associative with precedence 72 for @{'arrows2_OA $B $C}.
interpretation "'arrows2_OA" 'arrows2_OA A B = (arrows2 OA A B).

(* qui la notazione non va *)
lemma leq_to_eq_join: ∀S:OA.∀p,q:S. p ≤ q → q = (binary_join ? p q).
 intros;
 apply oa_leq_antisym;
  [ apply oa_density; intros;
    apply oa_overlap_sym;
    unfold binary_join; simplify;
    apply (. (oa_join_split : ?));
    exists; [ apply false ]
    apply oa_overlap_sym;
    assumption
  | unfold binary_join; simplify;
    apply (. (oa_join_sup : ?)); intro;
    cases i; whd in ⊢ (? ? ? ? ? % ?);
     [ assumption | apply oa_leq_refl ]]
qed.

lemma overlap_monotone_left: ∀S:OA.∀p,q,r:S. p ≤ q → p >< r → q >< r.
 intros;
 apply (. (leq_to_eq_join : ?)‡#);
  [ apply f;
  | skip
  | apply oa_overlap_sym;
    unfold binary_join; simplify;
    apply (. (oa_join_split : ?));
    exists [ apply true ]
    apply oa_overlap_sym;
    assumption; ]
qed.

(* Part of proposition 9.9 *)
lemma f_minus_image_monotone: ∀S,T.∀R:arrows2 OA S T.∀p,q. p ≤ q → R⎻ p ≤ R⎻ q.
 intros;
 apply (. (or_prop2 : ?));
 apply oa_leq_trans; [2: apply f; | skip | apply (. (or_prop2 : ?)^ -1); apply oa_leq_refl;]
qed.
 
(* Part of proposition 9.9 *)
lemma f_minus_star_image_monotone: ∀S,T.∀R:arrows2 OA S T.∀p,q. p ≤ q → R⎻* p ≤ R⎻* q.
 intros;
 apply (. (or_prop2 : ?)^ -1);
 apply oa_leq_trans; [3: apply f; | skip | apply (. (or_prop2 : ?)); apply oa_leq_refl;]
qed.

(* Part of proposition 9.9 *)
lemma f_image_monotone: ∀S,T.∀R:arrows2 OA S T.∀p,q. p ≤ q → R p ≤ R q.
 intros;
 apply (. (or_prop1 : ?));
 apply oa_leq_trans; [2: apply f; | skip | apply (. (or_prop1 : ?)^ -1); apply oa_leq_refl;]
qed.

(* Part of proposition 9.9 *)
lemma f_star_image_monotone: ∀S,T.∀R:arrows2 OA S T.∀p,q. p ≤ q → R* p ≤ R* q.
 intros;
 apply (. (or_prop1 : ?)^ -1);
 apply oa_leq_trans; [3: apply f; | skip | apply (. (or_prop1 : ?)); apply oa_leq_refl;]
qed.

lemma lemma_10_2_a: ∀S,T.∀R:arrows2 OA S T.∀p. p ≤ R⎻* (R⎻ p).
 intros;
 apply (. (or_prop2 : ?)^-1);
 apply oa_leq_refl.
qed.

lemma lemma_10_2_b: ∀S,T.∀R:arrows2 OA S T.∀p. R⎻ (R⎻* p) ≤ p.
 intros;
 apply (. (or_prop2 : ?));
 apply oa_leq_refl.
qed.

lemma lemma_10_2_c: ∀S,T.∀R:arrows2 OA S T.∀p. p ≤ R* (R p).
 intros;
 apply (. (or_prop1 : ?)^-1);
 apply oa_leq_refl.
qed.

lemma lemma_10_2_d: ∀S,T.∀R:arrows2 OA S T.∀p. R (R* p) ≤ p.
 intros;
 apply (. (or_prop1 : ?));
 apply oa_leq_refl.
qed.

lemma lemma_10_3_a: ∀S,T.∀R:arrows2 OA S T.∀p. R⎻ (R⎻* (R⎻ p)) = R⎻ p.
 intros; apply oa_leq_antisym;
  [ apply lemma_10_2_b;
  | apply f_minus_image_monotone;
    apply lemma_10_2_a; ]
qed.

lemma lemma_10_3_b: ∀S,T.∀R:arrows2 OA S T.∀p. R* (R (R* p)) = R* p.
 intros; apply oa_leq_antisym;
  [ apply f_star_image_monotone;
    apply (lemma_10_2_d ?? R p);
  | apply lemma_10_2_c; ]
qed.

lemma lemma_10_3_c: ∀S,T.∀R:arrows2 OA S T.∀p. R (R* (R p)) = R p.
 intros; apply oa_leq_antisym;
  [ apply lemma_10_2_d;
  | apply f_image_monotone;
    apply (lemma_10_2_c ?? R p); ]
qed.

lemma lemma_10_3_d: ∀S,T.∀R:arrows2 OA S T.∀p. R⎻* (R⎻ (R⎻* p)) = R⎻* p.
 intros; apply oa_leq_antisym;
  [ apply f_minus_star_image_monotone;
    apply (lemma_10_2_b ?? R p);
  | apply lemma_10_2_a; ]
qed.

lemma lemma_10_4_a: ∀S,T.∀R:arrows2 OA S T.∀p. R⎻* (R⎻ (R⎻* (R⎻ p))) = R⎻* (R⎻ p).
 intros; apply (†(lemma_10_3_a ?? R p));
qed.

lemma lemma_10_4_b: ∀S,T.∀R:arrows2 OA S T.∀p. R (R* (R (R* p))) = R (R* p).
intros; unfold in ⊢ (? ? ? % %); apply (†(lemma_10_3_b ?? R p));
qed.

lemma oa_overlap_sym': ∀o:OA.∀U,V:o. (U >< V) = (V >< U).
 intros; split; intro; apply oa_overlap_sym; assumption.
qed.
*)
