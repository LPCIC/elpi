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

include "pts_dummy/rc_sat.ma".
(*
(* HIGHER ORDER REDUCIBILITY CANDIDATES ***************************************)

(* An arity is a type of λ→ to be used as carrier for a h.o. r.c. *)

(* The type of the higher order r.c.'s having a given carrier.
 * a h.o. r.c is implemented as an inductively defined metalinguistic function
 * [ a CIC function in the present case ]. 
 *)
let rec HRC P ≝ match P with
   [ SORT     ⇒ RC
   | ABST Q P ⇒ HRC Q → HRC P
   ].

(* The default h.o r.c.
 * This is needed to complete the partial interpretation of types.
 *)
let rec defHRC P ≝ match P return λP. HRC P with
   [ SORT     ⇒ snRC
   | ABST Q P ⇒ λ_. defHRC P
   ].

(* extensional equality *******************************************************)

(* This is the extensional equalty of functions
 * modulo the extensional equality on the domain.
 * The functions may not respect extensional equality so reflexivity fails.
 *)
let rec hrceq P ≝ match P return λP. HRC P → HRC P → Prop with
   [ SORT     ⇒ λC1,C2. C1 ≅ C2
   | ABST Q P ⇒ λC1,C2. ∀B1,B2. hrceq Q B1 B2 → hrceq P (C1 B1) (C2 B2)
   ].

interpretation
   "extensional equality (h.o. reducibility candidate)"
   'Eq1 P C1 C2 = (hrceq P C1 C2).

lemma symmetric_hrceq: ∀P. symmetric ? (hrceq P).
#P (elim P) -P /4/
qed.

lemma transitive_hrceq: ∀P. transitive ? (hrceq P).
#P (elim P) -P /5/
qed.

lemma reflexive_defHRC: ∀P. defHRC P ≅^P defHRC P.
#P (elim P) -P (normalize) /2/
qed.
*)
