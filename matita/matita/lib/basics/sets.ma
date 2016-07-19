(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "basics/logic.ma".

(**** a subset of A is just an object of type A→Prop ****)

definition empty_set ≝ λA:Type[0].λa:A.False.
notation "\emptyv" non associative with precedence 90 for @{'empty_set}.
interpretation "empty set" 'empty_set = (empty_set ?).

definition singleton ≝ λA.λx,a:A.x=a.
(* notation "{x}" non associative with precedence 90 for @{'sing_lang $x}. *)
interpretation "singleton" 'singl x = (singleton ? x).

definition union : ∀A:Type[0].∀P,Q.A → Prop ≝ λA,P,Q,a.P a ∨ Q a.
interpretation "union" 'union a b = (union ? a b).

definition intersection : ∀A:Type[0].∀P,Q.A→Prop ≝ λA,P,Q,a.P a ∧ Q a.
interpretation "intersection" 'intersects a b = (intersection ? a b).

definition complement ≝ λU:Type[0].λA:U → Prop.λw.¬ A w.
interpretation "complement" 'not a = (complement ? a).

definition substraction := λU:Type[0].λA,B:U → Prop.λw.A w ∧ ¬ B w.
interpretation "substraction" 'minus a b = (substraction ? a b).

definition subset: ∀A:Type[0].∀P,Q:A→Prop.Prop ≝ λA,P,Q.∀a:A.(P a → Q a).
interpretation "subset" 'subseteq a b = (subset ? a b).

(* extensional equality *)
definition eqP ≝ λA:Type[0].λP,Q:A → Prop.∀a:A.P a ↔ Q a.
(* ≐ is typed as \doteq *)
notation "A ≐ B" non associative with precedence 45 for @{'eqP $A $B}.
interpretation "extensional equality" 'eqP a b = (eqP ? a b).

lemma eqP_sym: ∀U.∀A,B:U →Prop. 
  A ≐ B → B ≐ A.
#U #A #B #eqAB #a @iff_sym @eqAB qed.
 
lemma eqP_trans: ∀U.∀A,B,C:U →Prop. 
  A ≐ B → B ≐ C → A ≐ C.
#U #A #B #C #eqAB #eqBC #a @iff_trans // qed.

lemma eqP_union_r: ∀U.∀A,B,C:U →Prop. 
  A ≐ C  → A ∪ B ≐ C ∪ B.
#U #A #B #C #eqAB #a @iff_or_r @eqAB qed.
  
lemma eqP_union_l: ∀U.∀A,B,C:U →Prop. 
  B ≐ C  → A ∪ B ≐ A ∪ C.
#U #A #B #C #eqBC #a @iff_or_l @eqBC qed.
  
lemma eqP_intersect_r: ∀U.∀A,B,C:U →Prop. 
  A ≐ C  → A ∩ B ≐ C ∩ B.
#U #A #B #C #eqAB #a @iff_and_r @eqAB qed.
  
lemma eqP_intersect_l: ∀U.∀A,B,C:U →Prop. 
  B ≐ C  → A ∩ B ≐ A ∩ C.
#U #A #B #C #eqBC #a @iff_and_l @eqBC qed.

lemma eqP_substract_r: ∀U.∀A,B,C:U →Prop. 
  A ≐ C  → A - B ≐ C - B.
#U #A #B #C #eqAB #a @iff_and_r @eqAB qed.
  
lemma eqP_substract_l: ∀U.∀A,B,C:U →Prop. 
  B ≐ C  → A - B ≐ A - C.
#U #A #B #C #eqBC #a @iff_and_l /2/ qed.

(* set equalities *)
lemma union_empty_r: ∀U.∀A:U→Prop. 
  A ∪ ∅ ≐ A.
#U #A #w % [* // normalize #abs @False_ind /2/ | /2/]
qed.

lemma union_comm : ∀U.∀A,B:U →Prop. 
  A ∪ B ≐ B ∪ A.
#U #A #B #a % * /2/ qed. 

lemma union_assoc: ∀U.∀A,B,C:U → Prop. 
  A ∪ B ∪ C ≐ A ∪ (B ∪ C).
#S #A #B #C #w % [* [* /3/ | /3/] | * [/3/ | * /3/]
qed.   

lemma cap_comm : ∀U.∀A,B:U →Prop. 
  A ∩ B ≐ B ∩ A.
#U #A #B #a % * /2/ qed. 

lemma union_idemp: ∀U.∀A:U →Prop. 
  A ∪ A ≐ A.
#U #A #a % [* // | /2/] qed. 

lemma cap_idemp: ∀U.∀A:U →Prop. 
  A ∩ A ≐ A.
#U #A #a % [* // | /2/] qed. 

(*distributivities *)

lemma distribute_intersect : ∀U.∀A,B,C:U→Prop. 
  (A ∪ B) ∩ C ≐ (A ∩ C) ∪ (B ∩ C).
#U #A #B #C #w % [* * /3/ | * * /3/] 
qed.
  
lemma distribute_substract : ∀U.∀A,B,C:U→Prop. 
  (A ∪ B) - C ≐ (A - C) ∪ (B - C).
#U #A #B #C #w % [* * /3/ | * * /3/] 
qed.

(* substraction *)
lemma substract_def:∀U.∀A,B:U→Prop. A-B ≐ A ∩ ¬B.
#U #A #B #w normalize /2/
qed.