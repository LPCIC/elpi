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

include "pts_dummy/convertibility.ma".
include "pts_dummy/types.ma".
(*
(* PURE TYPE SYSTEMS OF THE λ-CUBE ********************************************)

inductive Cube_Ax: nat → nat → Prop ≝
  | star_box: Cube_Ax 0 1
.

(* The λPω pure type system (a.k.a. λC or CC) *********************************)

inductive CC_Re: nat → nat → nat → Prop ≝
   | star_star: CC_Re 0 0 0
   | box_star : CC_Re 1 0 0
   | box_box  : CC_Re 1 1 1
   | star_box : CC_Re 0 1 1
.

definition CC: pts ≝ mk_pts Cube_Ax CC_Re conv.

(* The λω pure type system (a.k.a. Fω) ****************************************)

inductive FO_Re: nat → nat → nat → Prop ≝
   | star_star: FO_Re 0 0 0
   | box_star : FO_Re 1 0 0
   | box_box  : FO_Re 1 1 1
.

definition FO: pts ≝ mk_pts Cube_Ax FO_Re conv.
*)
