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

include "formal_topology/basic_pairs.ma".
(*
(* carr1 e' necessario perche' ci sega via la coercion per gli oggetti di REL!
   (confondendola con la coercion per gli oggetti di SET
record concrete_space : Type[1] ≝
 { bp:> BP;
   converges: ∀a: carr1 (concr bp).∀U,V: carr1 (form bp). a ⊩ U → a ⊩ V → a ⊩ (U ↓ V);
   all_covered: ∀x: carr1 (concr bp). x ⊩ form bp
 }.

record convergent_relation_pair (CS1,CS2: concrete_space) : Type[1] ≝
 { rp:> arrows1 ? CS1 CS2;
   respects_converges:
    ∀b,c.
     minus_image ?? rp \sub\c (BPextS CS2 (b ↓ c)) =
     BPextS CS1 ((minus_image ?? rp \sub\f b) ↓ (minus_image ?? rp \sub\f c));
   respects_all_covered:
    minus_image ?? rp\sub\c (BPextS CS2 (full_subset (form CS2))) = BPextS CS1 (full_subset (form CS1))
 }.

definition convergent_relation_space_setoid: concrete_space → concrete_space → setoid1.
 intros;
 constructor 1;
  [ apply (convergent_relation_pair c c1)
  | constructor 1;
     [ intros;
       apply (relation_pair_equality c c1 c2 c3);
     | intros 1; apply refl1;
     | intros 2; apply sym1; 
     | intros 3; apply trans1]]
qed.

definition convergent_relation_space_composition:
 ∀o1,o2,o3: concrete_space.
  binary_morphism1
   (convergent_relation_space_setoid o1 o2)
   (convergent_relation_space_setoid o2 o3)
   (convergent_relation_space_setoid o1 o3).
 intros; constructor 1;
     [ intros; whd in c c1 ⊢ %;
       constructor 1;
        [ apply (fun1 ??? (comp1 BP ???)); [apply (bp o2) |*: apply rp; assumption]
        | intros;
          change in ⊢ (? ? ? (? ? ? (? ? ? %) ?) ?) with (c1 \sub \c ∘ c \sub \c);
          change in ⊢ (? ? ? ? (? ? ? ? (? ? ? ? ? (? ? ? (? ? ? %) ?) ?)))
            with (c1 \sub \f ∘ c \sub \f);
          change in ⊢ (? ? ? ? (? ? ? ? (? ? ? ? ? ? (? ? ? (? ? ? %) ?))))
            with (c1 \sub \f ∘ c \sub \f);
          apply (.= (extS_com ??????));
          apply (.= (†(respects_converges ?????)));
          apply (.= (respects_converges ?????));
          apply (.= (†(((extS_com ??????) \sup -1)‡(extS_com ??????)\sup -1)));
          apply refl1;
        | change in ⊢ (? ? ? (? ? ? (? ? ? %) ?) ?) with (c1 \sub \c ∘ c \sub \c);
          apply (.= (extS_com ??????));
          apply (.= (†(respects_all_covered ???)));
          apply (.= respects_all_covered ???);
          apply refl1]
     | intros;
       change with (b ∘ a = b' ∘ a');
       change in H with (rp'' ?? a = rp'' ?? a');
       change in H1 with (rp'' ?? b = rp ?? b');
       apply (.= (H‡H1));
       apply refl1]
qed.

definition CSPA: category1.
 constructor 1;
  [ apply concrete_space
  | apply convergent_relation_space_setoid
  | intro; constructor 1;
     [ apply id1
     | intros;
       unfold id; simplify;
       apply (.= (equalset_extS_id_X_X ??));
       apply (.= (†((equalset_extS_id_X_X ??)\sup -1‡
                    (equalset_extS_id_X_X ??)\sup -1)));
       apply refl1;
     | apply (.= (equalset_extS_id_X_X ??));
       apply refl1]
  | apply convergent_relation_space_composition
  | intros; simplify;
    change with (a34 ∘ (a23 ∘ a12) = (a34 ∘ a23) ∘ a12);
    apply (.= ASSOC1);
    apply refl1
  | intros; simplify;
    change with (a ∘ id1 ? o1 = a);
    apply (.= id_neutral_right1 ????);
    apply refl1
  | intros; simplify;
    change with (id1 ? o2 ∘ a = a);
    apply (.= id_neutral_left1 ????);
    apply refl1]
qed.
*)
*)
