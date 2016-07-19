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

include "hott/pts.ma".

record Exists (A: Type[0]) (P: A → Type[0]) : Type[0] ≝ {
 pr1: A;
 pr2: P pr1
}.

interpretation "Exists" 'exists x = (Exists ? x).
interpretation "mk_Exists" 'mk_exists w p = (mk_Exists ?? w p).
