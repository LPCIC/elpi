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

include "pts_dummy/ext_lambda.ma".
(*
(* STRONGLY NORMALIZING TERMS *************************************************)

(* SN(t) holds when t is strongly normalizing *)
(* FG: we axiomatize it for now because we dont have reduction yet *)
axiom SN: T → Prop.

(* lists of strongly normalizing terms *)
definition SNl ≝ all ? SN.

(* saturation conditions ******************************************************)

definition CR1 ≝ λ(P:?→Prop). ∀M. P M → SN M.

definition SAT0 ≝ λ(P:?→Prop). ∀n,l. SNl l → P (Appl (Sort n) l).

definition SAT1 ≝ λ(P:?->Prop). ∀i,l. SNl l → P (Appl (Rel i) l).

definition SAT2 ≝ λ(P:?→Prop). ∀N,L,M,l. SN N → SN L → 
                  P (Appl M[0:=L] l) → P (Appl (Lambda N M) (L::l)).

definition SAT3 ≝ λ(P:?→Prop). ∀M,N,l. P (Appl (D (App M N)) l) → 
                               P (Appl (D M) (N::l)).

definition SAT4 ≝ λ(P:?→Prop). ∀M. P M → P (D M).

lemma SAT0_sort: ∀P,n. SAT0 P → P (Sort n).
#P #n #HP @(HP n (nil ?) …) //
qed.

lemma SAT1_rel: ∀P,i. SAT1 P → P (Rel i).
#P #i #HP @(HP i (nil ?) …) //
qed.

lemma SAT3_1: ∀P,M,N. SAT3 P → P (D (App M N)) → P (App (D M) N).
#P #M #N #HP #H @(HP … ([])) @H
qed.

(* axiomatization *************************************************************)

axiom sn_sort: SAT0 SN.

axiom sn_rel: SAT1 SN.

axiom sn_beta: SAT2 SN.

axiom sn_dapp: SAT3 SN.

axiom sn_dummy: SAT4 SN.

axiom sn_lambda: ∀N,M. SN N → SN M → SN (Lambda N M).

axiom sn_prod: ∀N,M. SN N → SN M → SN (Prod N M).

axiom sn_inv_app_1: ∀M,N. SN (App M N) → SN M.
*)
