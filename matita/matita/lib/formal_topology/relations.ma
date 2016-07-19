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

include "formal_topology/subsets.ma".
(*
record binary_relation (A,B: SET) : Type[1] ≝
 { satisfy:> binary_morphism1 A B CPROP }.

notation < "hvbox (x \nbsp \natur term 90 r \nbsp y)"  with precedence 45 for @{'satisfy $r $x $y}.
notation > "hvbox (x \natur term 90 r y)"  with precedence 45 for @{'satisfy $r $x $y}.
interpretation "relation applied" 'satisfy r x y = (fun21 ??? (satisfy ?? r) x y).

definition binary_relation_setoid: SET → SET → setoid1.
 intros (A B);
 constructor 1;
  [ apply (binary_relation A B)
  | constructor 1;
     [ apply (λA,B.λr,r': binary_relation A B. ∀x,y. r x y ↔ r' x y)
     | simplify; intros 3; split; intro; assumption
     | simplify; intros 5; split; intro;
       [ apply (fi ?? (f ??)) | apply (if ?? (f ??))] assumption
     | simplify;  intros 7; split; intro;
        [ apply (if ?? (f1 ??)) | apply (fi ?? (f ??)) ]
        [ apply (if ?? (f ??)) | apply (fi ?? (f1 ??)) ]
       assumption]]
qed.

definition binary_relation_of_binary_relation_setoid : 
  ∀A,B.binary_relation_setoid A B → binary_relation A B ≝ λA,B,c.c.
coercion binary_relation_of_binary_relation_setoid.

definition composition:
 ∀A,B,C.
  (binary_relation_setoid A B) × (binary_relation_setoid B C) ⇒_1 (binary_relation_setoid A C).
 intros;
 constructor 1;
  [ intros (R12 R23);
    constructor 1;
    constructor 1;
     [ apply (λs1:A.λs3:C.∃s2:B. s1 ♮R12 s2 ∧ s2 ♮R23 s3);
     | intros;
       split; intro; cases e2 (w H3); clear e2; exists; [1,3: apply w ]
        [ apply (. (e^-1‡#)‡(#‡e1^-1)); assumption
        | apply (. (e‡#)‡(#‡e1)); assumption]]
  | intros 8; split; intro H2; simplify in H2 ⊢ %;
    cases H2 (w H3); clear H2; exists [1,3: apply w] cases H3 (H2 H4); clear H3;
    [ lapply (if ?? (e x w) H2) | lapply (fi ?? (e x w) H2) ]
    [ lapply (if ?? (e1 w y) H4)| lapply (fi ?? (e1 w y) H4) ]
    exists; try assumption;
    split; assumption]
qed.

definition REL: category1.
 constructor 1;
  [ apply setoid
  | intros (T T1); apply (binary_relation_setoid T T1)
  | intros; constructor 1;
    constructor 1; unfold setoid1_of_setoid; simplify;
     [ (* changes required to avoid universe inconsistency *)
       change with (carr o → carr o → CProp); intros; apply (eq ? c c1)
     | intros; split; intro; change in a a' b b' with (carr o);
       change in e with (eq ? a a'); change in e1 with (eq ? b b');
        [ apply (.= (e ^ -1));
          apply (.= e2);
          apply e1
        | apply (.= e);
          apply (.= e2);
          apply (e1 ^ -1)]]
  | apply composition
  | intros 9;
    split; intro;
    cases f (w H); clear f; cases H; clear H;
    [cases f (w1 H); clear f | cases f1 (w1 H); clear f1]
    cases H; clear H;
    exists; try assumption;
    split; try assumption;
    exists; try assumption;
    split; assumption
  |6,7: intros 5; unfold composition; simplify; split; intro;
        unfold setoid1_of_setoid in x y; simplify in x y;
        [1,3: cases e (w H1); clear e; cases H1; clear H1; unfold;
          [ apply (. (e : eq1 ? x w)‡#); assumption
          | apply (. #‡(e : eq1 ? w y)^-1); assumption]
        |2,4: exists; try assumption; split;
          (* change required to avoid universe inconsistency *)
          change in x with (carr o1); change in y with (carr o2);
          first [apply refl | assumption]]]
qed.

definition setoid_of_REL : objs1 REL → setoid ≝ λx.x.
coercion setoid_of_REL.

definition binary_relation_setoid_of_arrow1_REL : 
  ∀P,Q. arrows1 REL P Q → binary_relation_setoid P Q ≝ λP,Q,x.x.
coercion binary_relation_setoid_of_arrow1_REL.


notation > "B ⇒_\r1 C" right associative with precedence 72 for @{'arrows1_REL $B $C}.
notation "B ⇒\sub (\r 1) C" right associative with precedence 72 for @{'arrows1_REL $B $C}.
interpretation "'arrows1_REL" 'arrows1_REL A B = (arrows1 REL A B).
notation > "B ⇒_\r2 C" right associative with precedence 72 for @{'arrows2_REL $B $C}.
notation "B ⇒\sub (\r 2) C" right associative with precedence 72 for @{'arrows2_REL $B $C}.
interpretation "'arrows2_REL" 'arrows2_REL A B = (arrows2 (category2_of_category1 REL) A B).


definition full_subset: ∀s:REL. Ω^s.
 apply (λs.{x | True});
 intros; simplify; split; intro; assumption.
qed.

coercion full_subset.

definition comprehension: ∀b:REL. (b ⇒_1. CPROP) → Ω^b.
 apply (λb:REL. λP: b ⇒_1 CPROP. {x | P x});
 intros; simplify;
 apply (.= †e); apply refl1.
qed.

interpretation "subset comprehension" 'comprehension s p =
 (comprehension s (mk_unary_morphism1 ?? p ?)).

definition ext: ∀X,S:REL. (X ⇒_\r1 S) × S ⇒_1 (Ω^X).
 intros (X S); constructor 1; 
  [ apply (λr:X ⇒_\r1 S.λf:S.{x ∈ X | x ♮r f}); intros; simplify; apply (.= (e‡#)); apply refl1
  | intros; simplify; split; intros; simplify;
     [ change with (∀x. x ♮a b → x ♮a' b'); intros;
       apply (. (#‡e1^-1)); whd in e; apply (if ?? (e ??)); assumption
     | change with (∀x. x ♮a' b' → x ♮a b); intros;
       apply (. (#‡e1)); whd in e; apply (fi ?? (e ??));assumption]]
qed.

definition extS: ∀X,S:REL. ∀r:X ⇒_\r1 S. Ω^S ⇒_1 Ω^X.
 (* ∃ is not yet a morphism apply (λX,S,r,F.{x ∈ X | ∃a. a ∈ F ∧ x ♮r a});*)
 intros (X S r); constructor 1;
  [ intro F; constructor 1; constructor 1;
    [ apply (λx. x ∈ X ∧ ∃a:S. a ∈ F ∧ x ♮r a);
    | intros; split; intro; cases f (H1 H2); clear f; split;
       [ apply (. (e^-1‡#)); assumption
       |3: apply (. (e‡#)); assumption
       |2,4: cases H2 (w H3); exists; [1,3: apply w]
         [ apply (. (#‡(e^-1‡#))); assumption
         | apply (. (#‡(e‡#))); assumption]]]
  | intros; split; simplify; intros; cases f; cases e1; split;
     [1,3: assumption
     |2,4: exists; [1,3: apply w]
      [ apply (. (#‡e^-1)‡#); assumption
      | apply (. (#‡e)‡#); assumption]]]
qed.
(*
lemma equalset_extS_id_X_X: ∀o:REL.∀X.extS ?? (id1 ? o) X = X.
 intros;
 unfold extS; simplify;
 split; simplify;
  [ intros 2; change with (a ∈ X);
    cases f; clear f;
    cases H; clear H;
    cases x; clear x;
    change in f2 with (eq1 ? a w);
    apply (. (f2\sup -1‡#));
    assumption
  | intros 2; change in f with (a ∈ X);
    split;
     [ whd; exact I 
     | exists; [ apply a ]
       split;
        [ assumption
        | change with (a = a); apply refl]]]
qed.

lemma extS_com: ∀o1,o2,o3,c1,c2,S. extS o1 o3 (c2 ∘ c1) S = extS o1 o2 c1 (extS o2 o3 c2 S).
 intros; unfold extS; simplify; split; intros; simplify; intros;
  [ cases f (H1 H2); cases H2 (w H3); clear f H2; split; [assumption]
    cases H3 (H4 H5); cases H5 (w1 H6); clear H3 H5; cases H6 (H7 H8); clear H6;
    exists; [apply w1] split [2: assumption] constructor 1; [assumption]
    exists; [apply w] split; assumption
  | cases f (H1 H2); cases H2 (w H3); clear f H2; split; [assumption]
    cases H3 (H4 H5); cases H4 (w1 H6); clear H3 H4; cases H6 (w2 H7); clear H6;
    cases H7; clear H7; exists; [apply w2] split; [assumption] exists [apply w] split;
    assumption]
qed.
*)

(* the same as ⋄ for a basic pair *)
definition image: ∀U,V:REL. (U ⇒_\r1 V) ⇒_2 (Ω^U ⇒_2 Ω^V).
 intros; constructor 1;
 [ intro r; constructor 1;
   [ apply (λS: Ω^U. {y | ∃x:U. x ♮r y ∧ x ∈ S });
     intros; simplify; split; intro; cases e1; exists [1,3: apply w]
     [ apply (. (#‡e^-1)‡#); assumption
     | apply (. (#‡e)‡#); assumption]
   | intros; split; 
     [ intro y; simplify; intro yA; cases yA; exists; [ apply w ];
       apply (. #‡(#‡e^-1)); assumption;
     | intro y; simplify; intro yA; cases yA; exists; [ apply w ];
       apply (. #‡(#‡e)); assumption;]]
 | simplify; intros; intro y; simplify; split; simplify; intros (b H); cases H;
   exists; [1,3: apply w]; cases x; split; try assumption;
   [ apply (if ?? (e ??)); | apply (fi ?? (e ??)); ] assumption;]
qed.

(* the same as □ for a basic pair *)
definition minus_star_image: ∀U,V:REL. (U ⇒_\r1 V) ⇒_2 (Ω^U ⇒_2 Ω^V).
 intros; constructor 1; intros;
  [ constructor 1;
    [ apply (λS: Ω^U. {y | ∀x:U. x ♮c y → x ∈ S});
      intros; simplify; split; intros; apply f;
      [ apply (. #‡e); | apply (. #‡e ^ -1)] assumption;
    | intros; split; intro; simplify; intros;
      [ apply (. #‡e^-1);| apply (. #‡e); ] apply f; assumption;]
  | intros; intro; simplify; split; simplify; intros; apply f;
    [ apply (. (e x a2)); assumption | apply (. (e^-1 x a2)); assumption]]
qed.

(* the same as Rest for a basic pair *)
definition star_image: ∀U,V:REL. (U ⇒_\r1 V) ⇒_2 (Ω^V ⇒_2 Ω^U).
 intros; constructor 1;
  [ intro r; constructor 1; 
    [ apply (λS: Ω \sup V. {x | ∀y:V. x ♮r y → y ∈ S});
      intros; simplify; split; intros; apply f;
      [ apply (. e ‡#);| apply (. e^ -1‡#);] assumption;
    | intros; split; simplify; intros;
      [ apply (. #‡e^-1);| apply (. #‡e); ] apply f; assumption;]
  | intros; intro; simplify; split; simplify; intros; apply f; 
    [ apply (. e a2 y); | apply (. e^-1 a2 y)] assumption;]
qed.

(* the same as Ext for a basic pair *)
definition minus_image: ∀U,V:REL. (U ⇒_\r1 V) ⇒_2 (Ω^V ⇒_2 Ω^U).
 intros; constructor 1;
  [ intro r; constructor 1; 
    [ apply (λS: Ω^V. {x | ∃y:V. x ♮r y ∧ y ∈ S }).
      intros; simplify; split; intros; cases e1; cases x; exists; [1,3: apply w]
      split; try assumption; [ apply (. (e^-1‡#)); | apply (. (e‡#));] assumption;
    | intros; simplify; split; simplify; intros; cases e1; cases x; 
      exists [1,3: apply w] split; try assumption;
      [ apply (. (#‡e^-1)); | apply (. (#‡e));] assumption]
  | intros; intro; simplify; split; simplify; intros; cases e1; exists [1,3: apply w]
    cases x; split; try assumption;
    [ apply (. e^-1 a2 w); | apply (. e a2 w)] assumption;]
qed.

definition foo : ∀o1,o2:REL.carr1 (o1 ⇒_\r1 o2) → carr2 (setoid2_of_setoid1 (o1 ⇒_\r1 o2)) ≝ λo1,o2,x.x.

interpretation "relation f⎻*" 'OR_f_minus_star r = (fun12 ?? (minus_star_image ? ?) (foo ?? r)).
interpretation "relation f⎻" 'OR_f_minus r = (fun12 ?? (minus_image ? ?) (foo ?? r)).
interpretation "relation f*" 'OR_f_star r = (fun12 ?? (star_image ? ?) (foo ?? r)).

definition image_coercion: ∀U,V:REL. (U ⇒_\r1 V) → Ω^U ⇒_2 Ω^V.
intros (U V r Us); apply (image U V r); qed.
coercion image_coercion.

(* minus_image is the same as ext *)

theorem image_id: ∀o. (id1 REL o : carr2 (Ω^o ⇒_2 Ω^o)) =_1 (id2 SET1 Ω^o).
 intros; unfold image_coercion; unfold image; simplify;
 whd in match (?:carr2 ?);
  intro U; simplify; split; simplify; intros;
  [ change with (a ∈ U);
    cases e; cases x; change in e1 with (w =_1 a); apply (. e1^-1‡#); assumption
  | change in f with (a ∈ U);
    exists; [apply a] split; [ change with (a = a); apply refl1 | assumption]]
qed.

theorem minus_star_image_id: ∀o:REL. 
  ((id1 REL o)⎻* : carr2 (Ω^o ⇒_2 Ω^o)) =_1 (id2 SET1 Ω^o).
 intros; unfold minus_star_image; simplify; intro U; simplify; 
 split; simplify; intros;
  [ change with (a ∈ U); apply f; change with (a=a); apply refl1
  | change in f1 with (eq1 ? x a); apply (. f1‡#); apply f]
qed.

alias symbol "compose" (instance 5) = "category2 composition".
alias symbol "compose" (instance 4) = "category1 composition".
theorem image_comp: ∀A,B,C.∀r:B ⇒_\r1 C.∀s:A ⇒_\r1 B. 
  ((r ∘ s) : carr2 (Ω^A ⇒_2 Ω^C)) =_1 r ∘ s.
 intros; intro U; split; intro x; (unfold image; unfold SET1; simplify);
 intro H; cases H; 
 cases x1; [cases f|cases f1]; exists; [1,3: apply w1] cases x2; split; try assumption;
   exists; try assumption; split; assumption;
qed.

theorem minus_star_image_comp:
 ∀A,B,C.∀r:B ⇒_\r1 C.∀s:A ⇒_\r1 B.
  minus_star_image A C (r ∘ s) =_1 minus_star_image B C r ∘ (minus_star_image A B s).
 intros; unfold minus_star_image; intro X; simplify; split; simplify; intros;
 [ whd; intros; simplify; whd; intros; apply f; exists; try assumption; split; assumption;
 | cases f1; cases x1; apply f; assumption]
qed.


(*
(*CSC: unused! *)
theorem ext_comp:
 ∀o1,o2,o3: REL.
  ∀a: arrows1 ? o1 o2.
   ∀b: arrows1 ? o2 o3.
    ∀x. ext ?? (b∘a) x = extS ?? a (ext ?? b x).
 intros;
 unfold ext; unfold extS; simplify; split; intro; simplify; intros;
 cases f; clear f; split; try assumption;
  [ cases f2; clear f2; cases x1; clear x1; exists; [apply w] split;
     [1: split] assumption;
  | cases H; clear H; cases x1; clear x1; exists [apply w]; split;
     [2: cases f] assumption]
qed.
*)

axiom daemon : False.

theorem extS_singleton:
 ∀o1,o2.∀a.∀x.extS o1 o2 a {(x)} = ext o1 o2 a x. 
 intros; unfold extS; unfold ext; unfold singleton; simplify;
 split; intros 2; simplify; simplify in f; 
 [ cases f; cases e; cases x1; change in f2 with (x =_1 w); apply (. #‡f2); assumption;
 | split; try apply I; exists [apply x] split; try assumption; change with (x = x); apply rule #;] qed.
*)
