(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: ocaml.mli 14641 2011-11-06 11:59:10Z herbelin $ i*)

open Coq
open Miniml
open OcamlExtractionTable

val pp_decl : #status as 'status -> ml_decl -> 'status * std_ppcmds
val pp_spec : #status as 'status -> ml_spec -> 'status * std_ppcmds
val pp_open : #status as 'status -> string -> 'status * std_ppcmds
