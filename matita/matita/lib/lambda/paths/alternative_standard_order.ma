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

include "lambda/paths/standard_precedence.ma".

(* ALTERNATIVE STANDARD ORDER ***********************************************)

(* Note: this is p < q *)
definition slt: relation path ≝ TC … sprec.

interpretation "standard 'less than' on paths"
   'lt p q = (slt p q).

lemma slt_step_rc: ∀p,q. p ≺ q → p < q.
/2 width=1/
qed.

lemma slt_nil: ∀o,p. ◊ < o::p.
/2 width=1/
qed.

lemma slt_skip: dx::◊ < ◊.
/2 width=1/
qed.

lemma slt_comp: ∀o,p,q. p < q → o::p < o::q.
#o #p #q #H elim H -q /3 width=1/ /3 width=3/
qed.

theorem slt_trans: transitive … slt.
/2 width=3/
qed-.

lemma slt_refl: ∀p. p < p.
#p elim p -p /2 width=1/
@(slt_trans … (dx::◊)) //
qed.
