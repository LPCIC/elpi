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
include "formal_topology/notation.ma".
(*
record basic_pair: Type[1] ≝ { 
   concr: REL; form: REL; rel: concr ⇒_\r1 form
}.

interpretation "basic pair relation" 'Vdash2 x y c = (fun21 ??? (rel c) x y).
interpretation "basic pair relation (non applied)" 'Vdash c = (rel c).

record relation_pair (BP1,BP2: basic_pair): Type[1] ≝ { 
   concr_rel: (concr BP1) ⇒_\r1 (concr BP2); form_rel: (form BP1) ⇒_\r1 (form BP2);
   commute: comp1 REL ??? concr_rel (rel ?) =_1 form_rel ∘ ⊩
 }.

interpretation "concrete relation" 'concr_rel r = (concr_rel ?? r). 
interpretation "formal relation" 'form_rel r = (form_rel ?? r).

definition relation_pair_equality: ∀o1,o2. equivalence_relation1 (relation_pair o1 o2).
 intros; constructor 1; [ apply (λr,r'. ⊩ ∘ r \sub\c = ⊩ ∘ r' \sub\c);
  | simplify; intros; apply refl1;
  | simplify; intros 2; apply sym1;
  | simplify; intros 3; apply trans1; ]      
qed.

definition relation_pair_setoid: basic_pair → basic_pair → setoid1.
 intros;
 constructor 1;
  [ apply (relation_pair b b1)
  | apply relation_pair_equality
  ]
qed.

definition relation_pair_of_relation_pair_setoid :
  ∀P,Q. relation_pair_setoid P Q → relation_pair P Q ≝ λP,Q,x.x.
coercion relation_pair_of_relation_pair_setoid.

alias symbol "compose" (instance 1) = "category1 composition".
lemma eq_to_eq': 
  ∀o1,o2.∀r,r':relation_pair_setoid o1 o2. r =_1 r' → r \sub\f ∘ ⊩ =_1 r'\sub\f ∘ ⊩.
 intros 5 (o1 o2 r r' H);
 apply (.= (commute ?? r)^-1);
 change in H with (⊩ ∘ r \sub\c = ⊩ ∘ r' \sub\c);
 apply rule (.= H);
 apply (commute ?? r').
qed.

definition id_relation_pair: ∀o:basic_pair. relation_pair o o.
 intro;
 constructor 1;
  [1,2: apply id1;
  | lapply (id_neutral_right1 ? (concr o) ? (⊩)) as H;
    lapply (id_neutral_left1 ?? (form o) (⊩)) as H1;
    apply (.= H);
    apply (H1^-1);]
qed.

lemma relation_pair_composition: 
  ∀o1,o2,o3: basic_pair.
  relation_pair_setoid o1 o2 → relation_pair_setoid o2 o3 → relation_pair_setoid o1 o3.
intros 3 (o1 o2 o3);
  intros (r r1);
    constructor 1;
     [ apply (r1 \sub\c ∘ r \sub\c) 
     | apply (r1 \sub\f ∘ r \sub\f)
     | lapply (commute ?? r) as H;
       lapply (commute ?? r1) as H1;
       alias symbol "trans" = "trans1".
       alias symbol "assoc" = "category1 assoc".
       apply (.= ASSOC);
       apply (.= #‡H1);
       alias symbol "invert" = "setoid1 symmetry".
       apply (.= ASSOC ^ -1);
       apply (.= H‡#);
       apply ASSOC]
qed.

lemma relation_pair_composition_is_morphism:
  ∀o1,o2,o3: basic_pair.
  ∀a,a':relation_pair_setoid o1 o2.
  ∀b,b':relation_pair_setoid o2 o3.
   a=a' → b=b' →
    relation_pair_composition o1 o2 o3 a b
    = relation_pair_composition o1 o2 o3 a' b'.
intros 3 (o1 o2 o3);
    intros;
    change with (⊩ ∘ (b\sub\c ∘ a\sub\c) = ⊩ ∘ (b'\sub\c ∘ a'\sub\c));  
    change in e with (⊩ ∘ a \sub\c = ⊩ ∘ a' \sub\c);
    change in e1 with (⊩ ∘ b \sub\c = ⊩ ∘ b' \sub\c);
    apply (.= ASSOC);
    apply (.= #‡e1);
    apply (.= #‡(commute ?? b'));
    apply (.= ASSOC ^ -1);
    apply (.= e‡#);
    apply (.= ASSOC);
    apply (.= #‡(commute ?? b')^-1);
    apply (ASSOC ^ -1);
qed.

definition relation_pair_composition_morphism:
 ∀o1,o2,o3. binary_morphism1 (relation_pair_setoid o1 o2) (relation_pair_setoid o2 o3) (relation_pair_setoid o1 o3).
 intros;
 constructor 1;
  [ apply relation_pair_composition;
  | apply relation_pair_composition_is_morphism;]
qed.
    
lemma relation_pair_composition_morphism_assoc:
Πo1:basic_pair
.Πo2:basic_pair
 .Πo3:basic_pair
  .Πo4:basic_pair
   .Πa12:relation_pair_setoid o1 o2
    .Πa23:relation_pair_setoid o2 o3
     .Πa34:relation_pair_setoid o3 o4
      .relation_pair_composition_morphism o1 o3 o4
       (relation_pair_composition_morphism o1 o2 o3 a12 a23) a34
       =relation_pair_composition_morphism o1 o2 o4 a12
        (relation_pair_composition_morphism o2 o3 o4 a23 a34).
   intros;
    change with (⊩ ∘ (a34\sub\c ∘ (a23\sub\c ∘ a12\sub\c)) =
                 ⊩ ∘ ((a34\sub\c ∘ a23\sub\c) ∘ a12\sub\c));
    alias symbol "refl" = "refl1".
    alias symbol "prop2" = "prop21".
    apply (ASSOC‡#);
qed.    
    
lemma relation_pair_composition_morphism_respects_id:
  ∀o1,o2:basic_pair.∀a:relation_pair_setoid o1 o2.
  relation_pair_composition_morphism o1 o1 o2 (id_relation_pair o1) a=a.
   intros;
    change with (⊩ ∘ (a\sub\c ∘ (id_relation_pair o1)\sub\c) = ⊩ ∘ a\sub\c);
    apply ((id_neutral_right1 ????)‡#);    
qed.
    
lemma relation_pair_composition_morphism_respects_id_r:
  ∀o1,o2:basic_pair.∀a:relation_pair_setoid o1 o2.
  relation_pair_composition_morphism o1 o2 o2 a (id_relation_pair o2)=a.  
  intros;
    change with (⊩ ∘ ((id_relation_pair o2)\sub\c ∘ a\sub\c) = ⊩ ∘ a\sub\c);
    apply ((id_neutral_left1 ????)‡#);
qed.

definition BP: category1.
 constructor 1;
  [ apply basic_pair
  | apply relation_pair_setoid
  | apply id_relation_pair
  | apply relation_pair_composition_morphism
  | apply relation_pair_composition_morphism_assoc;
  | apply relation_pair_composition_morphism_respects_id;
  | apply relation_pair_composition_morphism_respects_id_r;]
qed.
  
definition basic_pair_of_BP : objs1 BP → basic_pair ≝ λx.x.
coercion basic_pair_of_BP.

definition relation_pair_setoid_of_arrows1_BP :
  ∀P,Q. arrows1 BP P Q → relation_pair_setoid P Q ≝ λP,Q,x.x.
coercion relation_pair_setoid_of_arrows1_BP.

(*
definition BPext: ∀o: BP. (form o) ⇒_1 Ω^(concr o).
 intros; constructor 1;
  [ apply (ext ? ? (rel o));
  | intros;
    apply (.= #‡e);
    apply refl1]
qed.

definition BPextS: ∀o: BP. Ω^(form o) ⇒_1 Ω^(concr o).
 intros; constructor 1;
  [ apply (minus_image ?? (rel o));
  | intros; apply (#‡e); ]
qed.

definition fintersects: ∀o: BP. (form o) × (form o) ⇒_1 Ω^(form o).
 intros (o); constructor 1;
  [ apply (λa,b: form o.{c | BPext o c ⊆ BPext o a ∩ BPext o b });
    intros; simplify; apply (.= (†e)‡#); apply refl1
  | intros; split; simplify; intros;
     [ apply (. #‡((†e^-1)‡(†e1^-1))); assumption
     | apply (. #‡((†e)‡(†e1))); assumption]]
qed.

interpretation "fintersects" 'fintersects U V = (fun21 ??? (fintersects ?) U V).

definition fintersectsS:
 ∀o:BP. Ω^(form o) × Ω^(form o) ⇒_1 Ω^(form o).
 intros (o); constructor 1;
  [ apply (λo: basic_pair.λa,b: Ω^(form o).{c | BPext o c ⊆ BPextS o a ∩ BPextS o b });
    intros; simplify; apply (.= (†e)‡#); apply refl1
  | intros; split; simplify; intros;
     [ apply (. #‡((†e^-1)‡(†e1^-1))); assumption
     | apply (. #‡((†e)‡(†e1))); assumption]]
qed.

interpretation "fintersectsS" 'fintersects U V = (fun21 ??? (fintersectsS ?) U V).

definition relS: ∀o: BP. (concr o) × Ω^(form o) ⇒_1 CPROP.
 intros (o); constructor 1;
  [ apply (λx:concr o.λS: Ω^(form o).∃y:form o.y ∈ S ∧ x ⊩⎽o y);
  | intros; split; intros; cases e2; exists [1,3: apply w]
     [ apply (. (#‡e1^-1)‡(e^-1‡#)); assumption
     | apply (. (#‡e1)‡(e‡#)); assumption]]
qed.

interpretation "basic pair relation for subsets" 'Vdash2 x y c = (fun21 (concr ?) ?? (relS c) x y).
interpretation "basic pair relation for subsets (non applied)" 'Vdash c = (fun21 ??? (relS c)).
*)
*)
