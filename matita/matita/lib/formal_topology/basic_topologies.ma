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
include "formal_topology/saturations.ma".
(*
record basic_topology: Type[1] ≝
 { carrbt:> REL;
   A: Ω^carrbt ⇒_1 Ω^carrbt;
   J: Ω^carrbt ⇒_1 Ω^carrbt;
   A_is_saturation: is_saturation ? A;
   J_is_reduction: is_reduction ? J;
   compatibility: ∀U,V. (A U ≬ J V) =_1 (U ≬ J V)
 }.

record continuous_relation (S,T: basic_topology) : Type[1] ≝
 { cont_rel:> S ⇒_\r1 T;
   reduced: ∀U. U =_1 J ? U → image_coercion ?? cont_rel U =_1 J ? (image_coercion ?? cont_rel U);
   saturated: ∀U. U =_1 A ? U → (cont_rel)⎻* U = _1A ? ((cont_rel)⎻* U)
 }. 

definition continuous_relation_setoid: basic_topology → basic_topology → setoid1.
 intros (S T); constructor 1;
  [ apply (continuous_relation S T)
  | constructor 1;
     [ apply (λr,s:continuous_relation S T.∀b. A ? (ext ?? r b) = A ? (ext ?? s b));
     | simplify; intros; apply refl1;
     | simplify; intros (x y H); apply sym1; apply H
     | simplify; intros; apply trans1; [2: apply f |3: apply f1; |1: skip]]]
qed.

definition continuos_relation_of_continuous_relation_setoid :
 ∀P,Q. continuous_relation_setoid P Q → continuous_relation P Q ≝ λP,Q,x.x.
coercion continuos_relation_of_continuous_relation_setoid.

axiom continuous_relation_eq':
 ∀o1,o2.∀a,a': continuous_relation_setoid o1 o2.
  a = a' → ∀X.a⎻* (A o1 X) = a'⎻* (A o1 X).
(*
 intros; split; intro; unfold minus_star_image; simplify; intros;
  [ cut (ext ?? a a1 ⊆ A ? X); [2: intros 2; apply (H1 a2); cases f1; assumption;]
    lapply (if ?? (A_is_saturation ???) Hcut); clear Hcut;
    cut (A ? (ext ?? a' a1) ⊆ A ? X); [2: apply (. (H ?)‡#); assumption]
    lapply (fi ?? (A_is_saturation ???) Hcut);
    apply (Hletin1 x); change with (x ∈ ext ?? a' a1); split; simplify;
     [ apply I | assumption ]
  | cut (ext ?? a' a1 ⊆ A ? X); [2: intros 2; apply (H1 a2); cases f1; assumption;]
    lapply (if ?? (A_is_saturation ???) Hcut); clear Hcut;
    cut (A ? (ext ?? a a1) ⊆ A ? X); [2: apply (. (H ?)\sup -1‡#); assumption]
    lapply (fi ?? (A_is_saturation ???) Hcut);
    apply (Hletin1 x); change with (x ∈ ext ?? a a1); split; simplify;
     [ apply I | assumption ]]
qed.*)

lemma continuous_relation_eq_inv':
 ∀o1,o2.∀a,a': continuous_relation_setoid o1 o2.
  (∀X.a⎻* (A o1 X) = a'⎻* (A o1 X)) → a=a'.
 intros 6;
 cut (∀a,a': continuous_relation_setoid o1 o2.
  (∀X.a⎻* (A o1 X) = a'⎻* (A o1 X)) → 
   ∀V:o2. A ? (ext ?? a' V) ⊆ A ? (ext ?? a V));
  [2: clear b f a' a; intros;
      lapply depth=0 (λV.saturation_expansive ??? (extS ?? a V)); [2: apply A_is_saturation;|skip]
       (* fundamental adjunction here! to be taken out *)
       cut (∀V:Ω^o2.V ⊆ a⎻* (A ? (extS ?? a V)));
        [2: intro; intros 2; unfold minus_star_image; simplify; intros;
            apply (Hletin V1 x); whd; split; [ exact I | exists; [apply a1] split; assumption]]
       clear Hletin;
       cut (∀V:Ω^o2.V ⊆ a'⎻* (A ? (extS ?? a V)));
        [2: intro; apply (. #‡(f ?)^-1); apply Hcut] clear f Hcut;
       (* second half of the fundamental adjunction here! to be taken out too *)
      intro; lapply (Hcut1 {(V)}); clear Hcut1;
      unfold minus_star_image in Hletin; unfold singleton in Hletin; simplify in Hletin;
      whd in Hletin; whd in Hletin:(?→?→%); simplify in Hletin;
      apply (if ?? (A_is_saturation ???));
      intros 2 (x H); lapply (Hletin V ? x ?);
       [ apply refl | unfold foo; apply H; ]
      change with (x ∈ A ? (ext ?? a V));
      apply (. #‡(†(extS_singleton ????)^-1));
      assumption;]
 split; apply Hcut; [2: assumption | intro; apply sym1; apply f]
qed.

definition continuous_relation_comp:
 ∀o1,o2,o3.
  continuous_relation_setoid o1 o2 →
   continuous_relation_setoid o2 o3 →
    continuous_relation_setoid o1 o3.
 intros (o1 o2 o3 r s); constructor 1;
  [ alias symbol "compose" (instance 1) = "category1 composition".
apply (s ∘ r)
  | intros;
    apply sym1;  
    (*change in ⊢ (? ? ? (? ? ? ? %) ?) with (image_coercion ?? (s ∘ r) U);*)
    apply (.= †(image_comp ??????));
    apply (.= (reduced ?? s (image_coercion ?? r U) ?)^-1); 
     [ apply (.= (reduced ?????)); [ assumption | apply refl1 ]
     | change in ⊢ (? ? ? % ?) with ((image_coercion ?? s ∘ image_coercion ?? r) U);
       apply (.= (image_comp ??????)^-1);
       apply refl1]
     | intros;
       apply sym1;
       apply (.= †(minus_star_image_comp ??? s r ?));
       apply (.= (saturated ?? s ((r)⎻* U) ?)^-1);
        [ apply (.= (saturated ?????)); [ assumption | apply refl1 ]
        | change in ⊢ (? ? ? % ?) with ((s⎻* ∘ r⎻* ) U);
          apply (.= (minus_star_image_comp ??????)^-1);
          apply refl1]]
qed.

definition BTop: category1.
 constructor 1;
  [ apply basic_topology
  | apply continuous_relation_setoid
  | intro; constructor 1;
     [ apply id1
     | intros;
       apply (.= (image_id ??));
       apply sym1;
       apply (.= †(image_id ??));
       apply sym1;
       assumption
     | intros;
       apply (.= (minus_star_image_id ??));
       apply sym1;
       apply (.= †(minus_star_image_id ??));
       apply sym1;
       assumption]
  | intros; constructor 1;
     [ apply continuous_relation_comp;
     | intros; simplify; intro x; simplify;
       lapply depth=0 (continuous_relation_eq' ???? e) as H';
       lapply depth=0 (continuous_relation_eq' ???? e1) as H1';
       letin K ≝ (λX.H1' ((a)⎻* (A ? X))); clearbody K;
       cut (∀X:Ω \sup o1.
              (b)⎻* (A o2 ((a)⎻* (A o1 X)))
            =_1 (b')⎻* (A o2 ((a')⎻* (A o1 X))));
        [2: intro; apply sym1; 
            apply (.= (†(†((H' X)^-1)))); apply sym1; apply (K X);]
       clear K H' H1';
alias symbol "powerset" (instance 5) = "powerset low".
alias symbol "compose" (instance 2) = "category1 composition".
cut (∀X:Ω^o1.
              ((b ∘ a))⎻* (A o1 X) =_1 ((b'∘a'))⎻* (A o1 X));
        [2: intro; unfold foo;
            apply (.= (minus_star_image_comp ??????));
            change in ⊢ (? ? ? % ?) with ((b)⎻* ((a)⎻* (A o1 X)));
            apply (.= †(saturated ?????));
             [ apply ((saturation_idempotent ????)^-1); apply A_is_saturation ]
            apply sym1; 
            apply (.= (minus_star_image_comp ??????));
            change in ⊢ (? ? ? % ?) with ((b')⎻* ((a')⎻* (A o1 X)));
            apply (.= †(saturated ?????));
             [ apply ((saturation_idempotent ????)^-1); apply A_is_saturation ]
           apply ((Hcut X)^-1)]
       clear Hcut; generalize in match x; clear x;
       apply (continuous_relation_eq_inv');
       apply Hcut1;]
  | intros; simplify; intro; do 2 (unfold continuous_relation_comp); simplify;
    alias symbol "trans" (instance 1) = "trans1".
alias symbol "refl" (instance 5) = "refl1".
alias symbol "prop2" (instance 3) = "prop21".
alias symbol "prop1" (instance 2) = "prop11".
alias symbol "assoc" (instance 4) = "category1 assoc".
apply (.= †(ASSOC‡#));
    apply refl1
  | intros; simplify; intro; unfold continuous_relation_comp; simplify;
    apply (.= †((id_neutral_right1 ????)‡#));
    apply refl1
  | intros; simplify; intro; simplify;
    apply (.= †((id_neutral_left1 ????)‡#));
    apply refl1]
qed.

(*
(*CSC: unused! *)
(* this proof is more logic-oriented than set/lattice oriented *)
theorem continuous_relation_eqS:
 ∀o1,o2:basic_topology.∀a,a': continuous_relation_setoid o1 o2.
  a = a' → ∀X. A ? (extS ?? a X) = A ? (extS ?? a' X).
 intros;
 cut (∀a: arrows1 ? o1 ?.∀x. x ∈ extS ?? a X → ∃y:o2.y ∈ X ∧ x ∈ ext ?? a y);
  [2: intros; cases f; clear f; cases H1; exists [apply w] cases x1; split;
      try assumption; split; assumption]
 cut (∀a,a':continuous_relation_setoid o1 o2.eq1 ? a a' → ∀x. x ∈ extS ?? a X → ∃y:o2. y ∈ X ∧ x ∈ A ? (ext ?? a' y));
  [2: intros; cases (Hcut ?? f); exists; [apply w] cases x1; split; try assumption;
      apply (. #‡(H1 ?));
      apply (saturation_expansive ?? (A_is_saturation o1) (ext ?? a1 w) x);
      assumption;] clear Hcut;
 split; apply (if ?? (A_is_saturation ???)); intros 2;
  [lapply (Hcut1 a a' H a1 f) | lapply (Hcut1 a' a (H \sup -1) a1 f)]
  cases Hletin; clear Hletin; cases x; clear x;
 cut (∀a: arrows1 ? o1 ?. ext ?? a w ⊆ extS ?? a X);
  [2,4: intros 3; cases f3; clear f3; simplify in f5; split; try assumption;
      exists [1,3: apply w] split; assumption;]
 cut (∀a. A ? (ext o1 o2 a w) ⊆ A ? (extS o1 o2 a X));
  [2,4: intros; apply saturation_monotone; try (apply A_is_saturation); apply Hcut;]
 apply Hcut2; assumption.
qed.
*)
*)
