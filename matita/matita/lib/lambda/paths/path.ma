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

(* PATH *********************************************************************)

(* Policy: path step metavariables: o *)
(* Note: this is a step of a path in the tree representation of a term:
         rc (rectus)  : proceed on the argument of an abstraction
         sn (sinister): proceed on the left argument of an application
         dx (dexter)  : proceed on the right argument of an application
*)
inductive step: Type[0] ≝
| rc: step
| sn: step
| dx: step
.

definition is_dx: predicate step ≝ λo. dx = o.

(* Policy: path metavariables: p, q *)
(* Note: this is a path in the tree representation of a term, heading to a redex *)
definition path: Type[0] ≝ list step.

definition compatible_rc: predicate (path→relation term) ≝ λR.
                          ∀p,A1,A2. R p A1 A2 → R (rc::p) (𝛌.A1) (𝛌.A2).

definition compatible_sn: predicate (path→relation term) ≝ λR.
                          ∀p,B1,B2,A. R p B1 B2 → R (sn::p) (@B1.A) (@B2.A).

definition compatible_dx: predicate (path→relation term) ≝ λR.
                          ∀p,B,A1,A2. R p A1 A2 → R (dx::p) (@B.A1) (@B.A2).

(* Note: a redex is "in the whd" when is not under an abstraction nor in the left argument of an application *)
definition in_whd: predicate path ≝ All … is_dx.

lemma in_whd_ind: ∀R:predicate path. R (◊) →
                  (∀p. in_whd p → R p → R (dx::p)) →
                  ∀p. in_whd p → R p.
#R #H #IH #p elim p -p // -H *
#p #IHp * #H1 #H2 destruct /3 width=1/
qed-.

(* Note: a redex is "inner" when is not in the whd *)
definition in_inner: predicate path ≝ λp. in_whd p → ⊥.

lemma in_inner_rc: ∀p. in_inner (rc::p).
#p * normalize #H destruct
qed.

lemma in_inner_sn: ∀p. in_inner (sn::p).
#p * normalize #H destruct
qed.

lemma in_inner_cons: ∀o,p. in_inner p → in_inner (o::p).
#o #p #H1p * /2 width=1/
qed.

lemma in_inner_inv_dx: ∀p. in_inner (dx::p) → in_inner p.
/3 width=1/
qed-.

lemma in_whd_or_in_inner: ∀p. in_whd p ∨ in_inner p.
#p elim p -p /2 width=1/ #o #p * #Hp /3 width=1/ cases o -o /2 width=1/ /3 width=1/
qed-.

lemma in_inner_ind: ∀R:predicate path.
                    (∀p. R (rc::p)) → (∀p. R (sn::p)) →
                    (∀p. in_inner p → R p → R (dx::p)) →
                    ∀p. in_inner p → R p.
#R #H1 #H2 #IH #p elim p -p
[ #H elim (H …) -H //
| * #p #IHp // #H
  lapply (in_inner_inv_dx … H) -H /3 width=1/
]
qed-.

lemma in_inner_inv: ∀p. in_inner p →
                    ∨∨ ∃q. rc::q = p | ∃q. sn::q = p
                     | ∃∃q. in_inner q & dx::q = p.
@in_inner_ind /3 width=2/ /3 width=3/
qed-.
