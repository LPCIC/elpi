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

include "pts_dummy/ext.ma".
(*
(* ARITIES ********************************************************************)

(* An arity is a normal term representing the functional structure of a term.
 * Arities can be freely applied as lon as the result is typable in λ→.
 * we encode an arity with a family of meta-linguistic functions typed by λ→
 * Such a family contains one member for each type of λ→ 
 *)

(* type of arity members ******************************************************)

(* the type of an arity member *)
inductive MEM: Type[0] ≝
   | TOP: MEM
   | FUN: MEM → MEM → MEM
.

definition pred ≝ λC. match C with
   [ TOP     ⇒ TOP
   | FUN _ A ⇒ A
   ].

definition decidable_MEq: ∀C1,C2:MEM. (C1 = C2) + (C1 ≠ C2).
#C1 (elim C1) -C1
   [ #C2 elim C2 -C2
     [ /2/
     | #B2 #A2 #_ #_ @inr @nmk #false destruct
     ]
   | #B1 #A1 #IHB1 #IHA1 #C2 elim C2 -C2
     [ @inr @nmk #false destruct
     | #B2 #A2 #_ #_ elim (IHB1 B2) -IHB1 #HB
       [ elim (IHA1 A2) - IHA1 #HA
         [ /2/ | @inr @nmk #false destruct elim HA /2/ ]
       | @inr @nmk #false destruct elim HB /2/
   ]
qed.

lemma fun_neq_sym: ∀A,C,B. pred C ≠ A → C ≠ FUN B A.
#A #C #B #HA elim HA -HA #HA @nmk #H @HA -HA >H //
qed. 

(* arity members **************************************************************)

(* the arity members of type TOP *)
inductive Top: Type[0] ≝
   | SORT: Top
. 

(* the arity members of type A *)
let rec Mem A ≝ match A with
   [ TOP     ⇒ Top
   | FUN B A ⇒ Mem B → Mem A
   ].

(* the members of the arity "sort" *)
let rec sort_mem A ≝ match A return λA. Mem A with
   [ TOP     ⇒ SORT
   | FUN B A ⇒ λ_.sort_mem A
   ]. 

(* arities ********************************************************************)

(* the type of arities *)
definition Arity ≝ ∀A. Mem A.

(* the arity "sort" *)
definition sort ≝ λA. sort_mem A.

(* the arity "constant" *)
definition const: ∀B. Mem B → Arity.
#B #x #A. elim (decidable_MEq B A) #H [ elim H @x | @(sort_mem A) ]
qed.

(* application of arities *)
definition aapp: MEM → Arity → Arity → Arity  ≝ λB,a,b,C. a (FUN B C) (b B).

(* abstraction of arities *)
definition aabst: (Arity → Arity) → Arity ≝
   λf,C. match C return λC. Mem C with
   [ TOP     ⇒ sort_mem TOP
   | FUN B A ⇒ λx. f (const B x) A
   ].

(* extensional equality of arity members **************************************)

(* Extensional equality of arity members (extensional equalty of functions).
 * The functions may not respect extensional equality so reflexivity fails
 * in general but may hold for specific arity members.
 *)
let rec ameq A ≝ match A return λA. Mem A → Mem A → Prop with
   [ TOP     ⇒ λa1,a2. a1 = a2
   | FUN B A ⇒ λa1,a2. ∀b1,b2. ameq B b1 b2 → ameq A (a1 b1) (a2 b2)
   ].

interpretation
   "extensional equality (arity member)"
   'Eq1 A a1 a2 = (ameq A a1 a2).

(* reflexivity of extensional equality for an arity member *)
definition invariant_mem ≝ λA,m. m ≅^A m.

interpretation
   "invariance (arity member)"
   'Invariant1 a A = (invariant_mem A a).


interpretation
   "invariance (arity member with implicit type)"
   'Invariant a = (invariant_mem ? a).

lemma symmetric_ameq: ∀A. symmetric ? (ameq A).
#A elim A -A /4/
qed.

lemma transitive_ameq: ∀A. transitive ? (ameq A).
#A elim A -A /5/
qed.

lemma invariant_sort_mem: ∀A. ! sort_mem A.
#A elim A normalize //
qed.

axiom const_eq: ∀A,x. const A x A ≅^A x.

axiom const_neq: ∀A,B,x. A ≠ B → const A x B ≅^B (sort_mem B).

(* extensional equality of arities ********************************************)

definition aeq: Arity → Arity → Prop ≝ λa1,a2. ∀A. a1 A ≅^A a2 A.

interpretation
   "extensional equality (arity)"
   'Eq a1 a2 = (aeq a1 a2).

definition invariant: Arity → Prop ≝ λa. a ≅ a.

interpretation
   "invariance (arity)"
   'Invariant a = (invariant a).

lemma symmetric_aeq: symmetric … aeq.
/2/ qed.

lemma transitive_aeq: transitive … aeq.
/2/ qed.

lemma const_comp: ∀A,x1,x2. x1 ≅^A x2 → const … x1 ≅ const … x2.
#A #x1 #x2 #Hx #C elim (decidable_MEq A C) #H
   [ <H @transitive_ameq; [2: @const_eq | skip ]
        @transitive_ameq; [2: @Hx | skip ]
        @symmetric_ameq //
   | @transitive_ameq; [2: @(const_neq … H) | skip ]
     @transitive_ameq; [2: @invariant_sort_mem | skip ]
     @symmetric_ameq /2/
   ]
qed.

lemma aapp_comp: ∀C,a1,a2,b1,b2. a1 ≅ a2 → b1 ≅ b2 → aapp C a1 b1 ≅ aapp C a2 b2.
#C #a1 #a2 #b1 #b2 #Ha #Hb #D @(Ha (FUN C D)) //
qed.

lemma aabst_comp: ∀f1,f2. (∀a1,a2. a1 ≅ a2 → f1 a1 ≅ f2 a2) →
                  aabst f1 ≅ aabst f2.
#f1 #f2 #H #C elim C -C // #B #A #_ #_ #b1 #b2 #Hb @H /2/
qed.

lemma invariant_sort: ! sort.
normalize //
qed.

(* "is a constant arity" *)
definition isc ≝ λa,A. const ? (a A) ≅ a.

lemma isc_sort: ∀A. isc sort A.
#A #C elim (decidable_MEq A C) #H [ <H // | /2 by const_neq/ ].
qed.

lemma isc_aapp: ∀B,A,b,a. ! b B → isc a A → isc (aapp B a b) (pred A).
#B #A #b #a #Hb #Ha #C elim (decidable_MEq (pred A) C) #H [ >H // ]
@transitive_ameq; [2: @(const_neq … H) | skip ]
lapply (transitive_ameq ????? (Ha (FUN B C))) -Ha [3: #Ha @Ha // |2: skip ]
@symmetric_ameq @const_neq /2/
qed.

(* extensional equality of arity contexts *************************************)

definition aceq ≝ λE1,E2. all2 … aeq E1 E2.

interpretation
   "extensional equality (arity context)"
   'Eq E1 E2 = (aceq E1 E2).

definition invariant_env: list Arity → Prop ≝ λE. E ≅ E.

interpretation
   "invariance (arity context)"
   'Invariant E = (invariant_env E).

lemma symmetric_aceq: symmetric … aceq.
/2/ qed.

lemma nth_sort_comp: ∀E1,E2. E1 ≅ E2 →
                     ∀i. nth i ? E1 sort ≅ nth i ? E2 sort.
#E1 #E2 #H #i @(all2_nth … aeq) //
qed.
*)
