(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: table.mli 14641 2011-11-06 11:59:10Z herbelin $ i*)

open Coq
open Miniml

type info
type db

class type g_status =
 object ('self)
  method ocaml_extraction_db: db
  method get_info: info * 'self
 end

class virtual status :
 object ('self)
  inherit g_status
  inherit NCic.status
  method set_ocaml_extraction_db: db -> 'self
  method set_ocaml_extraction_status: #g_status -> 'self
 end

val refresh_uri_in_info:
 refresh_uri_in_reference:(NReference.reference -> NReference.reference) ->
 refresh_uri:(NUri.uri -> NUri.uri) ->
  info -> info

val set_keywords : Idset.t -> unit

val register_infos: db -> info -> db

val to_be_included : #status as 'status -> NUri.uri -> 'status * bool

val open_file: #status as 'status -> baseuri:string -> string -> 'status
val print_ppcmds : #status -> in_ml:bool -> std_ppcmds -> unit
val close_file: #status as 'status -> 'status

val current_baseuri: #status -> string

val add_term : #status as 'status -> NReference.reference -> ml_decl -> 'status
val lookup_term : #status -> NReference.reference -> ml_decl

val add_type: #status as 'status -> NReference.reference -> ml_schema -> 'status
val lookup_type : #status -> NReference.reference -> ml_schema

val add_ind : #status as 'status -> ?dummy:bool -> NUri.uri -> ml_ind -> 'status
val lookup_ind : #status -> NUri.uri -> ml_ind

val add_global_ids: #status as 'status -> string -> 'status
val get_global_ids : #status -> Idset.t

val add_name_for_reference:
 #status as 'status -> NReference.reference -> string -> 'status
val name_of_reference : #status -> NReference.reference -> string

val add_modname: #status as 'status -> string -> 'status
val get_modnames : #status -> Idset.t

val add_modname_for_filename:
 #status as 'status -> string -> string -> 'status
val modname_of_filename : #status -> string -> string

val guess_projection:
 #status as 'status -> NUri.uri -> int -> 'status
val confirm_projection:
 #status as 'status -> NReference.reference -> 'status
val is_projection : #status -> NReference.reference -> bool
val projection_arity : #status -> NReference.reference -> int

val type_expand : unit -> bool

type opt_flag =
    { opt_kill_dum : bool; (* 1 *)
      opt_fix_fun : bool;   (* 2 *)
      opt_case_iot : bool;  (* 4 *)
      opt_case_idr : bool;  (* 8 *)
      opt_case_idg : bool;  (* 16 *)
      opt_case_cst : bool;  (* 32 *)
      opt_case_fun : bool;  (* 64 *)
      opt_case_app : bool;  (* 128 *)
      opt_let_app : bool;   (* 256 *)
      opt_lin_let : bool;   (* 512 *)
      opt_lin_beta : bool } (* 1024 *)

val optims :  unit -> opt_flag
