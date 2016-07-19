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

include "lambda/levels/term.ma".

(* ITERATED ABSTRACTION *****************************************************)

definition labst: nat → lterm → lterm ≝ λh,M. match M with
[ LVRef i e   ⇒ {i+h}§e
| LAppl i C A ⇒ {i+h}@C.A
].

interpretation "iterated abstraction (term by level)"
   'AnnotatedAbstraction h M = (labst h M).

interpretation "abstraction (term by level)"
   'Abstraction M = (labst (S O) M).

lemma labst_O: ∀M. 𝛌0.M = M.
* normalize //
qed.
