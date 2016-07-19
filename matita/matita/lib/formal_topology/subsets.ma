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
record powerset_carrier (A: objs1 SET) : Type[1] ≝ { mem_operator: A ⇒_1 CPROP }.
interpretation "powerset low" 'powerset A = (powerset_carrier A).
notation "hvbox(a break ∈. b)" non associative with precedence 45 for @{ 'mem_low $a $b }.
interpretation "memlow" 'mem_low a S = (fun11 ?? (mem_operator ? S) a).

definition subseteq_operator: ∀A: objs1 SET. Ω^A → Ω^A → CProp[0] ≝
 λA:objs1 SET.λU,V.∀a:A. a ∈. U → a ∈. V.

theorem transitive_subseteq_operator: ∀A. transitive2 ? (subseteq_operator A).
 intros 6; intros 2;
 apply s1; apply s;
 assumption.
qed.

definition powerset_setoid1: SET → SET1.
 intros (T);
 constructor 1;
  [ apply (powerset_carrier T)
  | constructor 1;
     [ apply (λU,V. subseteq_operator ? U V ∧ subseteq_operator ? V U)
     | simplify; intros; split; intros 2; assumption
     | simplify; intros (x y H); cases H; split; assumption
     | simplify; intros (x y z H H1); cases H; cases H1; split;
       apply transitive_subseteq_operator; [1,4: apply y ]
       assumption ]]
qed.

interpretation "powerset" 'powerset A = (powerset_setoid1 A).

interpretation "subset construction" 'subset \eta.x =
 (mk_powerset_carrier ? (mk_unary_morphism1 ? CPROP x ?)).

definition mem: ∀A. A × Ω^A ⇒_1 CPROP.
 intros;
 constructor 1;
  [ apply (λx,S. mem_operator ? S x)
  | intros 5;
    cases b; clear b; cases b'; clear b'; simplify; intros;
    apply (trans1 ????? (prop11 ?? u ?? e));
    cases e1; whd in s s1;
    split; intro;
     [ apply s; assumption
     | apply s1; assumption]]
qed.

interpretation "mem" 'mem a S = (fun21 ??? (mem ?) a S).

definition subseteq: ∀A. Ω^A × Ω^A ⇒_1 CPROP.
 intros;
 constructor 1;
  [ apply (λU,V. subseteq_operator ? U V)
  | intros;
    cases e; cases e1;
    split; intros 1;
    [ apply (transitive_subseteq_operator ????? s2);
      apply (transitive_subseteq_operator ???? s1 s4)
    | apply (transitive_subseteq_operator ????? s3);
      apply (transitive_subseteq_operator ???? s s4) ]]
qed.

interpretation "subseteq" 'subseteq U V = (fun21 ??? (subseteq ?) U V).

theorem subseteq_refl: ∀A.∀S:Ω^A.S ⊆ S.
 intros 4; assumption.
qed.

theorem subseteq_trans: ∀A.∀S1,S2,S3: Ω^A. S1 ⊆ S2 → S2 ⊆ S3 → S1 ⊆ S3.
 intros; apply transitive_subseteq_operator; [apply S2] assumption.
qed.

definition overlaps: ∀A. Ω^A × Ω^A ⇒_1 CPROP.
 intros;
 constructor 1;
  [ apply (λA:objs1 SET.λU,V:Ω^A.(exT2 ? (λx:A.x ∈ U) (λx:A.x ∈ V) : CProp[0]))
  | intros;
    constructor 1; intro; cases e2; exists; [1,4: apply w]
     [ apply (. #‡e^-1); assumption
     | apply (. #‡e1^-1); assumption
     | apply (. #‡e); assumption;
     | apply (. #‡e1); assumption]]
qed.

interpretation "overlaps" 'overlaps U V = (fun21 ??? (overlaps ?) U V).

definition intersects: ∀A. Ω^A × Ω^A ⇒_1 Ω^A.
 intros;
 constructor 1;
  [ apply rule (λU,V. {x | x ∈ U ∧ x ∈ V });
    intros; simplify; apply (.= (e‡#)‡(e‡#)); apply refl1;
  | intros;
    split; intros 2; simplify in f ⊢ %;
    [ apply (. (#‡e^-1)‡(#‡e1^-1)); assumption
    | apply (. (#‡e)‡(#‡e1)); assumption]]
qed.

interpretation "intersects" 'intersects U V = (fun21 ??? (intersects ?) U V).

definition union: ∀A. Ω^A × Ω^A ⇒_1 Ω^A.
 intros;
 constructor 1;
  [ apply (λU,V. {x | x ∈ U ∨ x ∈ V });
    intros; simplify; apply (.= (e‡#)‡(e‡#)); apply refl1
  | intros;
    split; intros 2; simplify in f ⊢ %;
    [ apply (. (#‡e^-1)‡(#‡e1^-1)); assumption
    | apply (. (#‡e)‡(#‡e1)); assumption]]
qed.

interpretation "union" 'union U V = (fun21 ??? (union ?) U V).

(* qua non riesco a mettere set *)
definition singleton: ∀A:setoid. A ⇒_1 Ω^A.
 intros; constructor 1;
  [ apply (λa:A.{b | a =_0 b}); unfold setoid1_of_setoid; simplify;
    intros; simplify;
    split; intro;
    apply (.= e1);
     [ apply e | apply (e^-1) ]
  | unfold setoid1_of_setoid; simplify;
    intros; split; intros 2; simplify in f ⊢ %; apply trans;
     [ apply a |4: apply a'] try assumption; apply sym; assumption]
qed.

interpretation "singleton" 'singl a = (fun11 ?? (singleton ?) a).
notation > "{ term 19 a : S }" with precedence 90 for @{fun11 ?? (singleton $S) $a}.

definition big_intersects: ∀A:SET.∀I:SET.(I ⇒_2 Ω^A) ⇒_2 Ω^A.
 intros; constructor 1;
  [ intro; whd; whd in I;
    apply ({x | ∀i:I. x ∈ c i});
    simplify; intros; split; intros; [ apply (. (e^-1‡#)); | apply (. e‡#); ]
    apply f;
  | intros; split; intros 2; simplify in f ⊢ %; intro;
     [ apply (. (#‡(e i)^-1)); apply f;
     | apply (. (#‡e i)); apply f]]
qed.

definition big_union: ∀A:SET.∀I:SET.(I ⇒_2 Ω^A) ⇒_2 Ω^A.
 intros; constructor 1;
  [ intro; whd; whd in A; whd in I;
    apply ({x | ∃i:I. x ∈ c i });
    simplify; intros; split; intros; cases e1; clear e1; exists; [1,3:apply w]
    [ apply (. (e^-1‡#)); | apply (. (e‡#)); ]
    apply x;
  | intros; split; intros 2; simplify in f ⊢ %; cases f; clear f; exists; [1,3:apply w]
     [ apply (. (#‡(e w)^-1)); apply x;
     | apply (. (#‡e w)); apply x]]
qed.

notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (⋃) \below (\emsp) term 90 p)" 
non associative with precedence 55 for @{ 'bigcup $p }.
notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (⋃) \below (ident i ∈  I) break term 90 p)" 
non associative with precedence 55 for @{ 'bigcup_mk (λ${ident i}:$I.$p) }.
notation > "hovbox(⋃ f)" non associative with precedence 65 for @{ 'bigcup $f }.

notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (⋂) \below (\emsp) term 90 p)" 
non associative with precedence 55 for @{ 'bigcap $p }.
notation < "hovbox(mstyle scriptlevel 1 scriptsizemultiplier 1.7 (⋂) \below (ident i ∈  I) break term 90 p)" 
non associative with precedence 55 for @{ 'bigcap_mk (λ${ident i}:$I.$p) }.
notation > "hovbox(⋂ f)" non associative with precedence 65 for @{ 'bigcap $f }.

interpretation "bigcup" 'bigcup f = (fun12 ?? (big_union ??) f).
interpretation "bigcap" 'bigcap f = (fun12 ?? (big_intersects ??) f).
interpretation "bigcup mk" 'bigcup_mk f = (fun12 ?? (big_union ??) (mk_unary_morphism2 ?? f ?)).
interpretation "bigcap mk" 'bigcap_mk f = (fun12 ?? (big_intersects ??) (mk_unary_morphism2 ?? f ?)).
*)
