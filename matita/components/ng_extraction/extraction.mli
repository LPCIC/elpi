(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: extraction.mli 14641 2011-11-06 11:59:10Z herbelin $ i*)

(*s Extraction from Coq terms to Miniml. *)

open Coq
open Miniml
open OcamlExtractionTable

val extract:
 #OcamlExtractionTable.status as 'status -> NCic.obj ->
  'status * ml_decl list * ml_spec list
