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

include "pts_dummy/ext.ma".
include "pts_dummy/subst.ma".
(*
(* MATTER CONCERNING STRONG NORMALIZATION TO BE PUT ELSEWHERE *****************)

(* substitution ***************************************************************)
(*
axiom is_dummy_lift: ∀p,t,k. is_dummy (lift t k p) = is_dummy t.
*)
(* FG: do we need this? 
definition lift0 ≝ λp,k,M . lift M p k. (**) (* remove definition *)

lemma lift_appl: ∀p,k,l,F. lift (Appl F l) p k = 
                             Appl (lift F p k) (map … (lift0 p k) l). 
#p #k #l (elim l) -l /2/ #A #D #IHl #F >IHl //
qed.
*)
(*
lemma lift_rel_lt: ∀i,p,k. (S i) ≤ k → lift (Rel i) k p = Rel i.
#i #p #k #Hik normalize >(le_to_leb_true … Hik) //
qed.
*)
lemma lift_rel_not_le: ∀i,p,k. (S i) ≰ k → lift (Rel i) k p = Rel (i+p).
#i #p #k #Hik normalize >(lt_to_leb_false (S i) k) /2/
qed.

lemma lift_app: ∀M,N,k,p.
                lift (App M N) k p = App (lift M k p) (lift N k p).
// qed.

lemma lift_lambda: ∀N,M,k,p. lift (Lambda N M) k p = 
                   Lambda (lift N k p) (lift M (k + 1) p).
// qed.

lemma lift_prod: ∀N,M,k,p.
                 lift (Prod N M) k p = Prod (lift N k p) (lift M (k + 1) p).
// qed.

lemma subst_app: ∀M,N,k,L. (App M N)[k≝L] = App M[k≝L] N[k≝L].
// qed.

lemma subst_lambda: ∀N,M,k,L. (Lambda N M)[k≝L] = Lambda N[k≝L] M[k+1≝L].
// qed.

lemma subst_prod: ∀N,M,k,L. (Prod N M)[k≝L] = Prod N[k≝L] M[k+1≝L].
// qed.


axiom lift_subst_lt: ∀A,B,i,j,k. lift (B[j≝A]) (j+k) i =
                     (lift B (j+k+1) i)[j≝lift A k i].

(* telescopic delifting substitution of l in M.
 * Rel 0 is replaced with the head of l
 *)
let rec tsubst M l on l ≝ match l with
   [ nil      ⇒ M
   | cons A D ⇒ (tsubst M[0≝A] D)
   ]. 

interpretation "telescopic substitution" 'Subst M l = (tsubst M l).

lemma tsubst_refl: ∀l,t. (lift t 0 (|l|))[/l] = t.
#l elim l -l; normalize // #hd #tl #IHl #t cut (S (|tl|) = |tl| + 1) // (**) (* eliminate cut *)
qed.

lemma tsubst_sort: ∀n,l. (Sort n)[/l] = Sort n.
// qed.
*)
