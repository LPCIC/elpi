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
include "formal_topology/notation.ma".
(*
record Obasic_pair: Type[2] ≝ { 
   Oconcr: OA; Oform: OA; Orel: arrows2 ? Oconcr Oform
}.

(* FIX *)
interpretation "o-basic pair relation indexed" 'Vdash2 x y c = (Orel c x y).
interpretation "o-basic pair relation (non applied)" 'Vdash c = (Orel c).

record Orelation_pair (BP1,BP2: Obasic_pair): Type[2] ≝ { 
   Oconcr_rel: (Oconcr BP1) ⇒_\o2 (Oconcr BP2); Oform_rel: (Oform BP1) ⇒_\o2 (Oform BP2);
   Ocommute: ⊩ ∘ Oconcr_rel =_2 Oform_rel ∘ ⊩
}.
 
(* FIX *)
interpretation "o-concrete relation" 'concr_rel r = (Oconcr_rel ?? r). 
interpretation "o-formal relation" 'form_rel r = (Oform_rel ?? r). 

definition Orelation_pair_equality:
 ∀o1,o2. equivalence_relation2 (Orelation_pair o1 o2).
 intros;
 constructor 1;
  [ apply (λr,r'. ⊩ ∘ r \sub\c = ⊩ ∘ r' \sub\c);
  | simplify;
    intros;
    apply refl2;
  | simplify;
    intros 2;
    apply sym2;
  | simplify;
    intros 3;
    apply trans2;
  ]      
qed.

(* qui setoid1 e' giusto: ma non lo e'!!! *)
definition Orelation_pair_setoid: Obasic_pair → Obasic_pair → setoid2.
 intros;
 constructor 1;
  [ apply (Orelation_pair o o1)
  | apply Orelation_pair_equality
  ]
qed.

definition Orelation_pair_of_Orelation_pair_setoid: 
  ∀P,Q. Orelation_pair_setoid P Q → Orelation_pair P Q ≝ λP,Q,x.x.
coercion Orelation_pair_of_Orelation_pair_setoid.

lemma eq_to_eq': ∀o1,o2.∀r,r': Orelation_pair_setoid o1 o2. r =_2 r' → r \sub\f ∘ ⊩ =_2 r'\sub\f ∘ ⊩.
 intros 5 (o1 o2 r r' H); change in H with (⊩ ∘ r\sub\c = ⊩ ∘ r'\sub\c);
 apply (.= ((Ocommute ?? r) ^ -1));
 apply (.= H);
 apply (.= (Ocommute ?? r'));
 apply refl2;
qed.


definition Oid_relation_pair: ∀o:Obasic_pair. Orelation_pair o o.
 intro;
 constructor 1;
  [1,2: apply id2;
  | lapply (id_neutral_right2 ? (Oconcr o) ? (⊩)) as H;
    lapply (id_neutral_left2 ?? (Oform o) (⊩)) as H1;
    apply (.= H);
    apply (H1^-1);]
qed.

lemma Orelation_pair_composition:
 ∀o1,o2,o3:Obasic_pair.
 Orelation_pair_setoid o1 o2 → Orelation_pair_setoid o2 o3→Orelation_pair_setoid o1 o3.
intros 3 (o1 o2 o3);
   intros (r r1);
    constructor 1;
     [ apply (r1 \sub\c ∘ r \sub\c) 
     | apply (r1 \sub\f ∘ r \sub\f)
     | lapply (Ocommute ?? r) as H;
       lapply (Ocommute ?? r1) as H1;
       apply rule (.= ASSOC);
       apply (.= #‡H1);
       apply rule (.= ASSOC ^ -1);
       apply (.= H‡#);
       apply rule ASSOC]
qed.


lemma Orelation_pair_composition_is_morphism:
  ∀o1,o2,o3:Obasic_pair.
  Πa,a':Orelation_pair_setoid o1 o2.Πb,b':Orelation_pair_setoid o2 o3.
   a=a' →b=b' →
      Orelation_pair_composition o1 o2 o3 a b
      = Orelation_pair_composition o1 o2 o3 a' b'.
intros;
    change with (⊩ ∘ (b\sub\c ∘ a\sub\c) = ⊩ ∘ (b'\sub\c ∘ a'\sub\c));  
    change in e with (⊩ ∘ a \sub\c = ⊩ ∘ a' \sub\c);
    change in e1 with (⊩ ∘ b \sub\c = ⊩ ∘ b' \sub\c);
    apply rule (.= ASSOC);
    apply (.= #‡e1);
    apply (.= #‡(Ocommute ?? b'));
    apply rule (.= ASSOC^-1);
    apply (.= e‡#);
    apply rule (.= ASSOC);
    apply (.= #‡(Ocommute ?? b')^-1);
    apply rule (ASSOC^-1);
qed.

definition Orelation_pair_composition_morphism:
 ∀o1,o2,o3. binary_morphism2 (Orelation_pair_setoid o1 o2) (Orelation_pair_setoid o2 o3) (Orelation_pair_setoid o1 o3).
intros; constructor 1;
[ apply Orelation_pair_composition;
| apply Orelation_pair_composition_is_morphism;]
qed.

lemma Orelation_pair_composition_morphism_assoc:
∀o1,o2,o3,o4:Obasic_pair
   .Πa12:Orelation_pair_setoid o1 o2
    .Πa23:Orelation_pair_setoid o2 o3
     .Πa34:Orelation_pair_setoid o3 o4
      .Orelation_pair_composition_morphism o1 o3 o4
       (Orelation_pair_composition_morphism o1 o2 o3 a12 a23) a34
       =Orelation_pair_composition_morphism o1 o2 o4 a12
        (Orelation_pair_composition_morphism o2 o3 o4 a23 a34).  
   intros;
    change with (⊩ ∘ (a34\sub\c ∘ (a23\sub\c ∘ a12\sub\c)) =
                 ⊩ ∘ ((a34\sub\c ∘ a23\sub\c) ∘ a12\sub\c));
    apply rule (ASSOC‡#);
qed.

lemma Orelation_pair_composition_morphism_respects_id:
Πo1:Obasic_pair
.Πo2:Obasic_pair
 .Πa:Orelation_pair_setoid o1 o2
  .Orelation_pair_composition_morphism o1 o1 o2 (Oid_relation_pair o1) a=a.
   intros;
    change with (⊩ ∘ (a\sub\c ∘ (Oid_relation_pair o1)\sub\c) = ⊩ ∘ a\sub\c);
    apply ((id_neutral_right2 ????)‡#);
qed.

lemma Orelation_pair_composition_morphism_respects_id_r:
Πo1:Obasic_pair
.Πo2:Obasic_pair
 .Πa:Orelation_pair_setoid o1 o2
  .Orelation_pair_composition_morphism o1 o2 o2 a (Oid_relation_pair o2)=a.
intros;
    change with (⊩ ∘ ((Oid_relation_pair o2)\sub\c ∘ a\sub\c) = ⊩ ∘ a\sub\c);
    apply ((id_neutral_left2 ????)‡#);
qed.

definition OBP: category2.
 constructor 1;
  [ apply Obasic_pair
  | apply Orelation_pair_setoid
  | apply Oid_relation_pair
  | apply Orelation_pair_composition_morphism
  | apply Orelation_pair_composition_morphism_assoc;
  | apply Orelation_pair_composition_morphism_respects_id;
  | apply Orelation_pair_composition_morphism_respects_id_r;]
qed.

definition Obasic_pair_of_objs2_OBP: objs2 OBP → Obasic_pair ≝ λx.x.
coercion Obasic_pair_of_objs2_OBP.

definition Orelation_pair_setoid_of_arrows2_OBP: 
  ∀P,Q.arrows2 OBP P Q → Orelation_pair_setoid P Q ≝ λP,Q,c.c.
coercion Orelation_pair_setoid_of_arrows2_OBP.

notation > "B ⇒_\obp2 C" right associative with precedence 72 for @{'arrows2_OBP $B $C}.
notation "B ⇒\sub (\obp 2) C" right associative with precedence 72 for @{'arrows2_OBP $B $C}.
interpretation "'arrows2_OBP" 'arrows2_OBP A B = (arrows2 OBP A B).

(*
definition BPext: ∀o: BP. form o ⇒ Ω \sup (concr o).
 intros; constructor 1;
  [ apply (ext ? ? (rel o));
  | intros;
    apply (.= #‡H);
    apply refl1]
qed.

definition BPextS: ∀o: BP. Ω \sup (form o) ⇒ Ω \sup (concr o) ≝
 λo.extS ?? (rel o).
*)

(*
definition fintersects: ∀o: BP. binary_morphism1 (form o) (form o) (Ω \sup (form o)).
 intros (o); constructor 1;
  [ apply (λa,b: form o.{c | BPext o c ⊆ BPext o a ∩ BPext o b });
    intros; simplify; apply (.= (†H)‡#); apply refl1
  | intros; split; simplify; intros;
     [ apply (. #‡((†H)‡(†H1))); assumption
     | apply (. #‡((†H\sup -1)‡(†H1\sup -1))); assumption]]
qed.

interpretation "fintersects" 'fintersects U V = (fun1 ??? (fintersects ?) U V).

definition fintersectsS:
 ∀o:BP. binary_morphism1 (Ω \sup (form o)) (Ω \sup (form o)) (Ω \sup (form o)).
 intros (o); constructor 1;
  [ apply (λo: basic_pair.λa,b: Ω \sup (form o).{c | BPext o c ⊆ BPextS o a ∩ BPextS o b });
    intros; simplify; apply (.= (†H)‡#); apply refl1
  | intros; split; simplify; intros;
     [ apply (. #‡((†H)‡(†H1))); assumption
     | apply (. #‡((†H\sup -1)‡(†H1\sup -1))); assumption]]
qed.

interpretation "fintersectsS" 'fintersects U V = (fun1 ??? (fintersectsS ?) U V).
*)

(*
definition relS: ∀o: BP. binary_morphism1 (concr o) (Ω \sup (form o)) CPROP.
 intros (o); constructor 1;
  [ apply (λx:concr o.λS: Ω \sup (form o).∃y: form o.y ∈ S ∧ x ⊩ y);
  | intros; split; intros; cases H2; exists [1,3: apply w]
     [ apply (. (#‡H1)‡(H‡#)); assumption
     | apply (. (#‡H1 \sup -1)‡(H \sup -1‡#)); assumption]]
qed.

interpretation "basic pair relation for subsets" 'Vdash2 x y = (fun1 (concr ?) ?? (relS ?) x y).
interpretation "basic pair relation for subsets (non applied)" 'Vdash = (fun1 ??? (relS ?)).
*)

notation "□ \sub b" non associative with precedence 90 for @{'box $b}.
notation > "□⎽term 90 b" non associative with precedence 90 for @{'box $b}.
interpretation "Universal image ⊩⎻*" 'box x = (fun12 ? ? (or_f_minus_star ? ?) (Orel x)).
 
notation "◊ \sub b" non associative with precedence 90 for @{'diamond $b}.
notation > "◊⎽term 90 b" non associative with precedence 90 for @{'diamond $b}.
interpretation "Existential image ⊩" 'diamond x = (fun12 ? ? (or_f ? ?) (Orel x)).

notation "'Rest' \sub b" non associative with precedence 90 for @{'rest $b}.
notation > "'Rest'⎽term 90 b" non associative with precedence 90 for @{'rest $b}.
interpretation "Universal pre-image ⊩*" 'rest x = (fun12 ? ? (or_f_star ? ?) (Orel x)).

notation "'Ext' \sub b" non associative with precedence 90 for @{'ext $b}.
notation > "'Ext'⎽term 90 b" non associative with precedence 90 for @{'ext $b}.
interpretation "Existential pre-image ⊩⎻" 'ext x = (fun12 ? ? (or_f_minus ? ?) (Orel x)).
*)
