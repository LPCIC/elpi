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

include "lambda/terms/term.ma".

(* ITERATED ABSTRACTION *****************************************************)

let rec abst d M on d ≝ match d with
[ O   ⇒ M
| S e ⇒ 𝛌. (abst e M)
].

interpretation "iterated abstraction (term)"
   'AnnotatedAbstraction d M = (abst d M).

lemma abst_plus: ∀A,m,n. 𝛌m+n.A = 𝛌m.𝛌n.A.
#A #m elim m -m normalize //
qed.
