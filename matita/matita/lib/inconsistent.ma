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

include "basics/logic.ma".

axiom boh: (False → False) = True.

definition J: False → False ≝ λf. match f in False with [ ].

definition I2: True ≝ match boh with [ refl ⇒ J ].

let rec err (u: True): False ≝ match u with [ I ⇒ err I2 ].

lemma oops: False ≝ err I.
