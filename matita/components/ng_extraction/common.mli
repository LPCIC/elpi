(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: common.mli 14641 2011-11-06 11:59:10Z herbelin $ i*)

open Coq
open Miniml
open Mlutil
open OcamlExtractionTable

(** By default, in module Format, you can do horizontal placing of blocks
    even if they include newlines, as long as the number of chars in the
    blocks are less that a line length. To avoid this awkward situation,
    we attach a big virtual size to [fnl] newlines. *)

val fnl : unit -> std_ppcmds
val space_if : bool -> std_ppcmds

val pp_par : bool -> std_ppcmds -> std_ppcmds
val pp_apply : std_ppcmds -> bool -> std_ppcmds list -> std_ppcmds
val pr_binding : identifier list -> std_ppcmds

type env = identifier list * Idset.t
val empty_env : #OcamlExtractionTable.status -> env

val fake_spec: NReference.spec

val rename_tvars: Idset.t -> identifier list -> identifier list
val push_vars : identifier list -> env -> identifier list * env
val get_db_name : int -> env -> identifier

(* true = capitalize *)
val modname_of_filename: #status as 'status-> bool -> string -> 'status * string

type kind = Term | Type | Cons

val pp_global :
 #status as 'status -> kind -> NReference.reference -> 'status * string
