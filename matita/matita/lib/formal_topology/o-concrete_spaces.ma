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

include "formal_topology/o-basic_pairs.ma".
include "formal_topology/o-saturations.ma".
(*
definition A : ∀b:OBP. unary_morphism1 (Oform b) (Oform b).
intros; constructor 1;
 [ apply (λx.□⎽b (Ext⎽b x));
 | intros; apply  (†(†e));]
qed.

lemma down_p : ∀S:SET1.∀I:SET.∀u:S ⇒_1 S.∀c:arrows2 SET1 I S.∀a:I.∀a':I.a =_1 a'→u (c a) =_1 u (c a').
intros; apply (†(†e));
qed.

record Oconcrete_space : Type[2] ≝
 { Obp:> OBP;
   (*distr : is_distributive (form bp);*)
   Odownarrow: unary_morphism1 (Oform Obp) (Oform Obp);
   Odownarrow_is_sat: is_o_saturation ? Odownarrow;
   Oconverges: ∀q1,q2.
     (Ext⎽Obp q1 ∧ (Ext⎽Obp q2)) = (Ext⎽Obp ((Odownarrow q1) ∧ (Odownarrow q2)));
   Oall_covered: Ext⎽Obp (oa_one (Oform Obp)) = oa_one (Oconcr Obp);
   Oil2: ∀I:SET.∀p:arrows2 SET1 I (Oform Obp).
     Odownarrow (∨ { x ∈ I | Odownarrow (p x) | down_p ???? }) =
     ∨ { x ∈ I | Odownarrow (p x) | down_p ???? };
   Oil1: ∀q.Odownarrow (A ? q) = A ? q
 }.

interpretation "o-concrete space downarrow" 'downarrow x = 
  (fun11 ?? (Odownarrow ?) x).

definition Obinary_downarrow : 
  ∀C:Oconcrete_space.binary_morphism1 (Oform C) (Oform C) (Oform C).
intros; constructor 1;
[ intros; apply (↓ c ∧ ↓ c1);
| intros;
  alias symbol "prop2" = "prop21".
  alias symbol "prop1" = "prop11".
  apply ((†e)‡(†e1));]
qed.

interpretation "concrete_space binary ↓" 'fintersects a b = (fun21 ? ? ? (Obinary_downarrow ?) a b).

record Oconvergent_relation_pair (CS1,CS2: Oconcrete_space) : Type[2] ≝
 { Orp:> arrows2 ? CS1 CS2;
   Orespects_converges:
    ∀b,c. eq1 ? (Orp\sub\c⎻ (Ext⎽CS2 (b ↓ c))) (Ext⎽CS1 (Orp\sub\f⎻ b ↓ Orp\sub\f⎻ c));
   Orespects_all_covered:
     eq1 ? (Orp\sub\c⎻ (Ext⎽CS2 (oa_one (Oform CS2))))
           (Ext⎽CS1 (oa_one (Oform CS1)))
 }.

definition Oconvergent_relation_space_setoid: Oconcrete_space → Oconcrete_space → setoid2.
 intros (c c1);
 constructor 1;
  [ apply (Oconvergent_relation_pair c c1)
  | constructor 1;
     [ intros (c2 c3);
       apply (Orelation_pair_equality c c1 c2 c3);
     | intros 1; apply refl2;
     | intros 2; apply sym2; 
     | intros 3; apply trans2]]
qed.

definition Oconvergent_relation_space_of_Oconvergent_relation_space_setoid: 
  ∀CS1,CS2.carr2 (Oconvergent_relation_space_setoid CS1 CS2) → 
    Oconvergent_relation_pair CS1 CS2  ≝ λP,Q,c.c.
coercion Oconvergent_relation_space_of_Oconvergent_relation_space_setoid.

definition Oconvergent_relation_space_composition:
 ∀o1,o2,o3: Oconcrete_space.
  binary_morphism2
   (Oconvergent_relation_space_setoid o1 o2)
   (Oconvergent_relation_space_setoid o2 o3)
   (Oconvergent_relation_space_setoid o1 o3).
 intros; constructor 1;
     [ intros; whd in t t1 ⊢ %;
       constructor 1;
        [ apply (c1 ∘ c);
        | intros;
          change in ⊢ (? ? ? % ?) with (c\sub\c⎻ (c1\sub\c⎻ (Ext⎽o3 (b↓c2))));
          alias symbol "trans" = "trans1".
          apply (.= († (Orespects_converges : ?)));
          apply (Orespects_converges ?? c (c1\sub\f⎻ b) (c1\sub\f⎻ c2));
        | change in ⊢ (? ? ? % ?) with (c\sub\c⎻ (c1\sub\c⎻ (Ext⎽o3 (oa_one (Oform o3)))));
          apply (.= (†(Orespects_all_covered :?)));
          apply rule (Orespects_all_covered ?? c);]
     | intros;
       change with (b ∘ a = b' ∘ a'); 
       change in e with (Orp ?? a = Orp ?? a');
       change in e1 with (Orp ?? b = Orp ?? b');
       apply (e‡e1);]
qed.

definition OCSPA: category2.
 constructor 1;
  [ apply Oconcrete_space
  | apply Oconvergent_relation_space_setoid
  | intro; constructor 1;
     [ apply id2
     | intros; apply refl1;
     | apply refl1]
  | apply Oconvergent_relation_space_composition
  | intros; simplify; whd in a12 a23 a34;
    change with (a34 ∘ (a23 ∘ a12) = (a34 ∘ a23) ∘ a12);
    apply rule ASSOC;
  | intros; simplify;
    change with (a ∘ id2 OBP o1 = a);
    apply (id_neutral_right2 : ?);
  | intros; simplify;
    change with (id2 ? o2 ∘ a = a);
    apply (id_neutral_left2 : ?);]
qed.

definition Oconcrete_space_of_OCSPA : objs2 OCSPA → Oconcrete_space ≝ λx.x.
coercion Oconcrete_space_of_OCSPA.

definition Oconvergent_relation_space_setoid_of_arrows2_OCSPA :
 ∀P,Q. arrows2 OCSPA P Q → Oconvergent_relation_space_setoid P Q ≝ λP,Q,x.x.
coercion Oconvergent_relation_space_setoid_of_arrows2_OCSPA.

*)
