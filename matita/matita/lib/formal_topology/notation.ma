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
(*
notation "hvbox (r \sub \c)"  with precedence 90 for @{'concr_rel $r}.
notation "hvbox (r \sub \f)"  with precedence 90 for @{'form_rel $r}.

definition hide ≝ λA:Type.λx:A.x.

interpretation "hide" 'hide x = (hide ? x). 
*)