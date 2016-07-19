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

include "formal_topology/relations.ma".
include "formal_topology/o-algebra.ma".
(*
definition POW': objs1 SET → OAlgebra.
 intro A; constructor 1;
  [ apply (Ω^A);
  | apply subseteq;
  | apply overlaps;
  | apply big_intersects;
  | apply big_union;
  | apply ({x | True});
    simplify; intros; apply (refl1 ? (eq1 CPROP));
  | apply ({x | False});
    simplify; intros; apply (refl1 ? (eq1 CPROP));
  | intros; whd; intros; assumption
  | intros; whd; split; assumption
  | intros; apply transitive_subseteq_operator; [2: apply f; | skip | assumption]
  | intros; cases f; exists [apply w] assumption
  | intros; split; [ intros 4; apply (f ? f1 i); | intros 3; intro; apply (f i ? f1); ]
  | intros; split;
     [ intros 4; apply f; exists; [apply i] assumption;
     | intros 3; intros; cases f1; apply (f w a x); ]
  | intros 3; cases f;
  | intros 3; constructor 1;
  | intros; cases f; exists; [apply w]
     [ assumption
     | whd; intros; cases i; simplify; assumption]
  | intros; split; intro;
     [ (** screenshot "screen-pow". *) cases f; cases x1; exists [apply w1] exists [apply w] assumption;
     | cases e; cases x; exists; [apply w1] [ assumption | exists; [apply w] assumption]]
  | intros; intros 2; cases (f {(a)} ?); 
     [ exists; [apply a] [assumption | change with (a = a); apply refl1;]
     | change in x1 with (a = w); change with (mem A a q); apply (. (x1‡#));
       assumption]]
qed.

definition powerset_of_POW': ∀A.oa_P (POW' A) → Ω^A ≝ λA,x.x.
coercion powerset_of_POW'.

definition orelation_of_relation: ∀o1,o2:REL. o1 ⇒_\r1 o2 → (POW' o1) ⇒_\o2 (POW' o2).
 intros;
 constructor 1;
  [ apply rule c;
  | apply rule (c⎻* ); 
  | apply rule (c* );
  | apply rule (c⎻);
  | intros; split; intro;
     [ intros 2; intros 2; apply (f y); exists[apply a] split; assumption;
     | intros 2; change with (a ∈ q); cases f1; cases x; clear f1 x; 
       apply (f w f3); assumption; ]
  | unfold foo; intros; split; intro;
     [ intros 2; intros 2; apply (f x); exists [apply a] split; assumption;
     | intros 2; change with (a ∈ q); cases f1; cases x; apply (f w f3); assumption;]
  | intros; split; unfold foo; unfold image_coercion; simplify; intro; cases f; clear f;
     [ cases x; cases x2; clear x x2; exists; [apply w1]
        [ assumption | exists; [apply w] split; assumption]
     | cases x1; cases x2; clear x1 x2; exists; [apply w1]
        [ exists; [apply w] split; assumption;
        | assumption; ]]]
qed.

lemma orelation_of_relation_preserves_equality:
 ∀o1,o2:REL.∀t,t': o1 ⇒_\r1 o2. 
   t = t' → orelation_of_relation ?? t =_2 orelation_of_relation ?? t'.
 intros; split; unfold orelation_of_relation; unfold foo; simplify;
 change in e with (t =_2 t'); unfold image_coercion; apply (†e);
qed.

lemma minus_image_id : ∀o:REL.((id1 REL o))⎻ =_1 (id2 SET1 Ω^o).
unfold foo; intro o; intro; unfold minus_image; simplify; split; simplify; intros;
[ cases e; cases x; change with (a1 ∈ a); change in f with (a1 =_1 w); 
  apply (. f‡#); assumption;
| change in f with (a1 ∈ a); exists [ apply a1] split; try assumption; 
  change with (a1 =_1 a1); apply refl1;]
qed.

lemma star_image_id : ∀o:REL.  ((id1 REL o))* =_1 (id2 SET1 Ω^o).
unfold foo; intro o; intro; unfold star_image; simplify; split; simplify; intros;
[ change with (a1 ∈ a); apply f; change with (a1 =_1 a1); apply rule refl1;
| change in f1 with (a1 =_1 y); apply (. f1^-1‡#); apply f;]
qed.
    
lemma orelation_of_relation_preserves_identity:
 ∀o1:REL. orelation_of_relation ?? (id1 ? o1) =_2 id2 OA (POW' o1).
 intros; split; 
 (unfold orelation_of_relation; unfold OA; unfold foo; simplify);
 [ apply (minus_star_image_id o1);
 | apply (minus_image_id o1); 
 | apply (image_id o1);
 | apply (star_image_id o1) ]
qed.
 
(*
  split; whd; intro; 
  [ change with ((∀x. x ♮(id1 REL o1) a1→x∈a) → a1 ∈ a); intros;
    apply (f a1); change with (a1 = a1); apply refl1;
  | change with (a1 ∈ a → ∀x. x ♮(id1 REL o1) a1→x∈a); intros;
    change in f1 with (x = a1); apply (. f1‡#); apply f;
  | alias symbol "and" = "and_morphism".
    change with ((∃y:o1.a1 ♮(id1 REL o1) y ∧ y∈a) → a1 ∈ a);
    intro; cases e; clear e; cases x; clear x; change in f with (a1=w);
    apply (. f‡#); apply f1;
  | change with (a1 ∈ a → ∃y:o1.a1 ♮(id1 REL o1) y ∧ y∈a);
    intro; exists; [apply a1]; split; [ change with (a1=a1); apply refl1; | apply f]
  | change with ((∃x:o1.x ♮(id1 REL o1) a1∧x∈a) → a1 ∈ a);
    intro; cases e; clear e; cases x; clear x; change in f with (w=a1);
    apply (. f^-1‡#); apply f1;
  | change with (a1 ∈ a → ∃x:o1.x ♮(id1 REL o1) a1∧x∈a);
    intro; exists; [apply a1]; split; [ change with (a1=a1); apply refl1; | apply f]
  | change with ((∀y.a1 ♮(id1 REL o1) y→y∈a) → a1 ∈ a); intros;
    apply (f a1); change with (a1 = a1); apply refl1;
  | change with (a1 ∈ a → ∀y.a1 ♮(id1 REL o1) y→y∈a); intros;
    change in f1 with (a1 = y); apply (. f1^-1‡#); apply f;]
qed.
*)

(* CSC: ???? forse un uncertain mancato *)
alias symbol "eq" = "setoid2 eq".
alias symbol "compose" = "category1 composition".
lemma orelation_of_relation_preserves_composition:
 ∀o1,o2,o3:REL.∀F: o1 ⇒_\r1 o2.∀G: o2 ⇒_\r1 o3.
  orelation_of_relation ?? (G ∘ F) = 
  comp2 OA ??? (orelation_of_relation ?? F) (orelation_of_relation ?? G).
 intros; split; intro; split; whd; intro; whd in ⊢ (% → %); intros;
  [ whd; intros; apply f; exists; [ apply x] split; assumption; 
  | cases f1; clear f1; cases x1; clear x1; apply (f w); assumption;
  | cases e; cases x; cases f; cases x1; clear e x f x1; exists; [ apply w1 ]
    split; [ assumption | exists; [apply w] split; assumption ]
  | cases e; cases x; cases f1; cases x1; clear e x f1 x1; exists; [apply w1 ]
    split; [ exists; [apply w] split; assumption | assumption ]
  | unfold arrows1_of_ORelation_setoid; 
    cases e; cases x; cases f; cases x1; clear e x f x1; exists; [ apply w1 ]
    split; [ assumption | exists; [apply w] split; assumption ]
  | unfold arrows1_of_ORelation_setoid in e; 
    cases e; cases x; cases f1; cases x1; clear e x f1 x1; exists; [apply w1 ]
    split; [ exists; [apply w] split; assumption | assumption ]
  | whd; intros; apply f; exists; [ apply y] split; assumption;
  | cases f1; clear f1; cases x; clear x; apply (f w); assumption;]
qed.

definition POW: carr3 (arrows3 CAT2 (category2_of_category1 REL) OA).
 constructor 1;
  [ apply POW';
  | intros; constructor 1;
     [ apply (orelation_of_relation S T);
     | intros; apply (orelation_of_relation_preserves_equality S T a a' e); ]
  | apply orelation_of_relation_preserves_identity;
  | apply orelation_of_relation_preserves_composition; ]
qed.

theorem POW_faithful: faithful2 ?? POW.
 intros 5; unfold POW in e; simplify in e; cases e;
 unfold orelation_of_relation in e3; simplify in e3; clear e e1 e2 e4;
 intros 2; simplify; unfold image_coercion in e3; cases (e3 {(x)});
 split; intro; [ lapply (s y); | lapply (s1 y); ]
  [2,4: exists; [1,3:apply x] split; [1,3: assumption |*: change with (x=x); apply rule #]
  |*: cases Hletin; cases x1; change in f3 with (x =_1 w); apply (. f3‡#); assumption;]
qed.


(*
lemma currify: ∀A,B,C. (A × B ⇒_1 C) → A → (B ⇒_1 C).
intros; constructor 1; [ apply (b c); | intros; apply (#‡e);]
qed.
*)

include "formal_topology/notation.ma".

theorem POW_full: full2 ?? POW. 
 intros 3 (S T); exists;
  [ constructor 1; constructor 1;
     [ apply (λx:carr S.λy:carr T. y ∈ f {(x)});
     | apply hide; intros; unfold FunClass_1_OF_carr2; lapply (.= e1‡#);
        [4: apply mem; |6: apply Hletin;|1,2,3,5: skip]
       lapply (#‡prop11 ?? f ?? (†e)); [6: apply Hletin; |*:skip ]]  
     | (split; intro; split; simplify);
           [ change with (∀a1.(∀x. a1 ∈ (f {(x):S}) → x ∈ a) → a1 ∈ f⎻* a);
           | change with (∀a1.a1 ∈ f⎻* a → (∀x.a1 ∈ f {(x):S} → x ∈ a)); 
           | alias symbol "and" (instance 4) = "and_morphism".
change with (∀a1.(∃y:carr T. y ∈ f {(a1):S} ∧ y ∈ a) → a1 ∈ f⎻ a);
           | alias symbol "and" (instance 2) = "and_morphism".
change with (∀a1.a1 ∈ f⎻ a → (∃y:carr T.y ∈ f {(a1):S} ∧ y ∈ a)); 
           | alias symbol "and" (instance 3) = "and_morphism".
change with (∀a1.(∃x:carr S. a1 ∈ f {(x):S} ∧ x ∈ a) → a1 ∈ f a);
           | change with (∀a1.a1 ∈. f a → (∃x:carr S. a1 ∈ f {(x):S} ∧ x ∈ a));
           | change with (∀a1.(∀y. y ∈ f {(a1):S} → y ∈ a) → a1 ∈ f* a);
           | change with (∀a1.a1 ∈ f* a → (∀y. y ∈ f {(a1):S} → y ∈ a)); ]
        [ intros; apply ((. (or_prop2 ?? f (singleton ? a1) a)^-1) ? a1);
           [ intros 2; apply (f1 a2); change in f2 with (a2 ∈ f⎻ (singleton ? a1));
             lapply (. (or_prop3 ?? f (singleton ? a2) (singleton ? a1)));
              [ cases Hletin; change in x1 with (eq1 ? a1 w);
                apply (. x1‡#); assumption;
              | exists; [apply a2] [change with (a2=a2); apply rule #; | assumption]]
           | change with (a1 = a1); apply rule #; ]
        | intros; apply ((. (or_prop2 ?? f (singleton ? a1) a)) ? x);
           [ intros 2; change in f3 with (eq1 ? a1 a2); change with (a2 ∈ f⎻* a); apply (. f3^-1‡#);
             assumption;
           | lapply (. (or_prop3 ?? f (singleton ? x) (singleton ? a1))^-1);
              [ cases Hletin; change in x1 with (eq1 ? x w);
                change with (x ∈ f⎻ (singleton ? a1)); apply (. x1‡#); assumption;
              | exists; [apply a1] [assumption | change with (a1=a1); apply rule #; ]]]
        | intros; cases e; cases x; clear e x;
          lapply (. (or_prop3 ?? f (singleton ? a1) a)^-1);
           [ cases Hletin; change in x with (eq1 ? a1 w1); apply (. x‡#); assumption;
           | exists; [apply w] assumption ]
        | intros; lapply (. (or_prop3 ?? f (singleton ? a1) a));
           [ cases Hletin; exists; [apply w] split; assumption;
           | exists; [apply a1] [change with (a1=a1); apply rule #; | assumption ]] 
        | intros; cases e; cases x; clear e x;
          apply (f_image_monotone ?? f (singleton ? w) a ? a1);
           [ intros 2; change in f3 with (eq1 ? w a2); change with (a2 ∈ a);
             apply (. f3^-1‡#); assumption;
           | assumption; ]
        | intros; lapply (. (or_prop3 ?? f a (singleton ? a1))^-1);
           [ cases Hletin; exists; [apply w] split;
              [ lapply (. (or_prop3 ?? f (singleton ? w) (singleton ? a1)));
                 [ cases Hletin1; change in x3 with (eq1 ? a1 w1); apply (. x3‡#); assumption;
                 | exists; [apply w] [change with (w=w); apply rule #; | assumption ]]
              | assumption ]
           | exists; [apply a1] [ assumption; | change with (a1=a1); apply rule #;]]
        | intros; apply ((. (or_prop1 ?? f (singleton ? a1) a)^-1) ? a1);
           [ apply f1; | change with (a1=a1); apply rule #; ]
        | intros; apply ((. (or_prop1 ?? f (singleton ? a1) a)) ? y);
           [ intros 2; change in f3 with (eq1 ? a1 a2); change with (a2 ∈ f* a);
             apply (. f3^-1‡#); assumption;
           | assumption ]]]
qed.
*)
