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

include "formal_topology/o-algebra.ma".
include "formal_topology/o-saturations.ma".
(*
record Obasic_topology: Type[2] ≝ { 
   Ocarrbt:> OA;
   oA: Ocarrbt ⇒_2 Ocarrbt; oJ: Ocarrbt ⇒_2 Ocarrbt;
   oA_is_saturation: is_o_saturation ? oA; oJ_is_reduction: is_o_reduction ? oJ;
   Ocompatibility: ∀U,V. (oA U >< oJ V) =_1 (U >< oJ V)
 }.

record Ocontinuous_relation (S,T: Obasic_topology) : Type[2] ≝ { 
   Ocont_rel:> arrows2 OA S T;
   Oreduced: ∀U:S. U = oJ ? U → Ocont_rel U =_1 oJ ? (Ocont_rel U);
   Osaturated: ∀U:S. U = oA ? U → Ocont_rel⎻* U =_1 oA ? (Ocont_rel⎻* U)
 }. 

definition Ocontinuous_relation_setoid: Obasic_topology → Obasic_topology → setoid2.
 intros (S T); constructor 1;
  [ apply (Ocontinuous_relation S T)
  | constructor 1;
     [ alias symbol "eq" = "setoid2 eq".
       alias symbol "compose" = "category2 composition".
       apply (λr,s:Ocontinuous_relation S T. (r⎻* ) ∘ (oA S) = (s⎻* ∘ (oA ?)));
     | simplify; intros; apply refl2;
     | simplify; intros; apply sym2; apply e
     | simplify; intros; apply trans2; [2: apply e |3: apply e1; |1: skip]]]
qed.

definition Ocontinuous_relation_of_Ocontinuous_relation_setoid: 
  ∀P,Q. Ocontinuous_relation_setoid P Q → Ocontinuous_relation P Q ≝ λP,Q,c.c.
coercion Ocontinuous_relation_of_Ocontinuous_relation_setoid.

(*
theorem continuous_relation_eq':
 ∀o1,o2.∀a,a': continuous_relation_setoid o1 o2.
  a = a' → ∀X.a⎻* (A o1 X) = a'⎻* (A o1 X).
 intros; apply oa_leq_antisym; intro; unfold minus_star_image; simplify; intros;
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
qed.

theorem continuous_relation_eq_inv':
 ∀o1,o2.∀a,a': continuous_relation_setoid o1 o2.
  (∀X.a⎻* (A o1 X) = a'⎻* (A o1 X)) → a=a'.
 intros 6;
 cut (∀a,a': continuous_relation_setoid o1 o2.
  (∀X.a⎻* (A o1 X) = a'⎻* (A o1 X)) → 
   ∀V:(oa_P (carrbt o2)). A o1 (a'⎻ V) ≤ A o1 (a⎻ V));
  [2: clear b H a' a; intros;
      lapply depth=0 (λV.saturation_expansive ??? (extS ?? a V)); [2: apply A_is_saturation;|skip]
       (* fundamental adjunction here! to be taken out *)
       cut (∀V:Ω \sup o2.V ⊆ minus_star_image ?? a (A ? (extS ?? a V)));
        [2: intro; intros 2; unfold minus_star_image; simplify; intros;
            apply (Hletin V1 x); whd; split; [ exact I | exists; [apply a1] split; assumption]]
       clear Hletin;
       cut (∀V:Ω \sup o2.V ⊆ minus_star_image ?? a' (A ? (extS ?? a V)));
        [2: intro; apply (. #‡(H ?)); apply Hcut] clear H Hcut;
       (* second half of the fundamental adjunction here! to be taken out too *)
      intro; lapply (Hcut1 (singleton ? V)); clear Hcut1;
      unfold minus_star_image in Hletin; unfold singleton in Hletin; simplify in Hletin;
      whd in Hletin; whd in Hletin:(?→?→%); simplify in Hletin;
      apply (if ?? (A_is_saturation ???));
      intros 2 (x H); lapply (Hletin V ? x ?);
       [ apply refl | cases H; assumption; ]
      change with (x ∈ A ? (ext ?? a V));
      apply (. #‡(†(extS_singleton ????)));
      assumption;]
 split; apply Hcut; [2: assumption | intro; apply sym1; apply H]
qed.
*)

definition Ocontinuous_relation_comp:
 ∀o1,o2,o3.
  Ocontinuous_relation_setoid o1 o2 →
   Ocontinuous_relation_setoid o2 o3 →
    Ocontinuous_relation_setoid o1 o3.
 intros (o1 o2 o3 r s); constructor 1;
  [ apply (s ∘ r);
  | intros;
    apply sym1; 
    change in match ((s ∘ r) U) with (s (r U));
    apply (.= (Oreduced : ?)^-1);
     [ apply (.= (Oreduced :?)); [ assumption | apply refl1 ]
     | apply refl1]
  | intros;
    apply sym1;
    change in match ((s ∘ r)⎻* U) with (s⎻* (r⎻* U));
    apply (.= (Osaturated : ?)^-1);
     [ apply (.= (Osaturated : ?)); [ assumption | apply refl1 ]
     | apply refl1]]
qed.

definition OBTop: category2.
 constructor 1;
  [ apply Obasic_topology
  | apply Ocontinuous_relation_setoid
  | intro; constructor 1;
     [ apply id2
     | intros; apply e;
     | intros; apply e;]
  | intros; constructor 1;
     [ apply Ocontinuous_relation_comp;
     | intros; simplify;
       change with ((b⎻* ∘ a⎻* ) ∘ oA o1 = ((b'⎻* ∘ a'⎻* ) ∘ oA o1)); 
       change with (b⎻* ∘ (a⎻* ∘ oA o1) = b'⎻* ∘ (a'⎻* ∘ oA o1));
       change in e with (a⎻* ∘ oA o1 = a'⎻* ∘ oA o1);
       change in e1 with (b⎻* ∘ oA o2 = b'⎻* ∘ oA o2);
       apply (.= e‡#);
       intro x;          
       change with (b⎻* (a'⎻* (oA o1 x)) =_1 b'⎻*(a'⎻* (oA o1 x))); 
       apply (.= †(Osaturated o1 o2 a' (oA o1 x) ?)); [
         apply ((o_saturation_idempotent ?? (oA_is_saturation o1) x)^-1);]
       apply (.= (e1 (a'⎻* (oA o1 x))));
       change with (b'⎻* (oA o2 (a'⎻* (oA o1 x))) =_1 b'⎻*(a'⎻* (oA o1 x)));   
       apply (.= †(Osaturated o1 o2 a' (oA o1 x):?)^-1); [
         apply ((o_saturation_idempotent ?? (oA_is_saturation o1) x)^-1);]
       apply rule #;]
  | intros; simplify;
    change with (((a34⎻* ∘ a23⎻* ) ∘ a12⎻* ) ∘ oA o1 = ((a34⎻* ∘ (a23⎻* ∘ a12⎻* )) ∘ oA o1));
    apply rule (#‡ASSOC ^ -1);
  | intros; simplify;
    change with ((a⎻* ∘ (id2 ? o1)⎻* ) ∘ oA o1 = a⎻* ∘ oA o1);
    apply (#‡(id_neutral_right2 : ?));
  | intros; simplify;
    change with (((id2 ? o2)⎻* ∘ a⎻* ) ∘ oA o1 = a⎻* ∘ oA o1);
    apply (#‡(id_neutral_left2 : ?));]
qed.

definition Obasic_topology_of_OBTop: objs2 OBTop → Obasic_topology ≝ λx.x.
coercion Obasic_topology_of_OBTop.

definition Ocontinuous_relation_setoid_of_arrows2_OBTop : 
  ∀P,Q. arrows2 OBTop P Q → Ocontinuous_relation_setoid P Q ≝ λP,Q,x.x.
coercion Ocontinuous_relation_setoid_of_arrows2_OBTop.

notation > "B ⇒_\obt2 C" right associative with precedence 72 for @{'arrows2_OBT $B $C}.
notation "B ⇒\sub (\obt 2) C" right associative with precedence 72 for @{'arrows2_OBT $B $C}.
interpretation "'arrows2_OBT" 'arrows2_OBT A B = (arrows2 OBTop A B).


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
