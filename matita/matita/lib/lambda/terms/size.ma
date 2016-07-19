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

include "lambda/terms/relocation.ma".

(* SIZE *********************************************************************)

(* Note: this gives the number of abstractions and applications in M *)
let rec size M on M ≝ match M with
[ VRef i   ⇒ 0
| Abst A   ⇒ size A + 1
| Appl B A ⇒ (size B) + (size A) + 1
].

interpretation "term size"
   'card M = (size M).

lemma size_lift: ∀h,M,d. |↑[d, h] M| = |M|.
#h #M elim M -M normalize //
qed.
