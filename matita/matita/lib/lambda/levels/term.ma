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

include "lambda/background/preamble.ma".

(* PER LEVEL TERM STRUCTURE *************************************************)

(* Policy: term metavariables          : A, B, C, D, M, N
           relative level metavariables: i, j
           absolute level metavariables: d, e
*)
(* Bote: first argument: relative level of the term *)
inductive lterm: Type[0] ≝
| LVRef: nat  → nat  → lterm          (* variable reference by level *)
| LAppl: nat  → lterm → lterm → lterm (* function application        *)
.

interpretation "stratified term construction (variable reference by level)"
   'VariableReferenceByLevel i d = (LVRef i d).

interpretation "stratified term construction (application)"
   'Application i C A = (LAppl i C A).

notation "hvbox( { term 46 b } § break term 90 d )"
 non associative with precedence 46
 for @{ 'VariableReferenceByLevel $b $d }.
