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

include "lambda/paths/trace.ma".

(* DECOMPOSED TRACE *********************************************************)

(* Policy: decomposed trace metavariables: P, Q *)
(* Note: this is a binary tree on traces *)
inductive dtrace: Type[0] ≝
| tree_nil : dtrace
| tree_cons: trace → dtrace → dtrace → dtrace
.

let rec size (P:dtrace) on P ≝ match P with
[ tree_nil          ⇒ 0
| tree_cons s Q1 Q2 ⇒ size Q2 + size Q1 + |s|
].

interpretation "decomposed trace size" 'card P = (size P).
