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

(* SUBSETS OF SUBTERMS ******************************************************)

(* Policy: boolean marks metavariables: b,c
           subterms metavariables: F,G,T,U,V,W
*)
(* Note: each subterm is marked with true if it belongs to the subset *)
inductive subterms: Type[0] ≝
| SVRef: bool → nat  → subterms
| SAbst: bool → subterms → subterms
| SAppl: bool → subterms → subterms → subterms
.

interpretation "subterms construction (variable reference by index)"
   'VariableReferenceByIndex b i = (SVRef b i).

interpretation "subterms construction (abstraction)"
   'Abstraction b T = (SAbst b T).

interpretation "subterms construction (application)"
   'Application b V T = (SAppl b V T).

(*
definition compatible_abst: predicate (relation term) ≝ λR.
                            ∀A1,A2. R A1 A2 → R (𝛌.A1) (𝛌.A2).

definition compatible_sn: predicate (relation term) ≝ λR.
                          ∀A,B1,B2. R B1 B2 → R (@B1.A) (@B2.A).

definition compatible_dx: predicate (relation term) ≝ λR.
                          ∀B,A1,A2. R A1 A2 → R (@B.A1) (@B.A2).

definition compatible_appl: predicate (relation term) ≝ λR.
                            ∀B1,B2. R B1 B2 → ∀A1,A2. R A1 A2 →
                            R (@B1.A1) (@B2.A2).

lemma star_compatible_abst: ∀R. compatible_abst R → compatible_abst (star … R).
#R #HR #A1 #A2 #H elim H -A2 // /3 width=3/
qed.

lemma star_compatible_sn: ∀R. compatible_sn R → compatible_sn (star … R).
#R #HR #A #B1 #B2 #H elim H -B2 // /3 width=3/
qed.

lemma star_compatible_dx: ∀R. compatible_dx R → compatible_dx (star … R).
#R #HR #B #A1 #A2 #H elim H -A2 // /3 width=3/
qed.

lemma star_compatible_appl: ∀R. reflexive ? R →
                            compatible_appl R → compatible_appl (star … R).
#R #H1R #H2R #B1 #B2 #H elim H -B2 /3 width=1/ /3 width=5/
qed.
*)
