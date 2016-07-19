(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

exception Parse_error of string
exception Level_not_found of int

type db

class type g_status =
 object
  method notation_parser_db: db
 end

class virtual status: keywords:string list ->
 object('self)
  inherit NCic.status
  inherit g_status
  method set_notation_parser_db: db -> 'self
  method set_notation_parser_status: 'status. #g_status as 'status -> 'self
 end

type checked_l1_pattern = private CL1P of NotationPt.term * int

val refresh_uri_in_checked_l1_pattern:
 refresh_uri_in_term:(NCic.term -> NCic.term) ->
 refresh_uri_in_reference:(NReference.reference -> NReference.reference) ->
  checked_l1_pattern -> checked_l1_pattern 

(** {2 Parsing functions} *)

  (** concrete syntax pattern: notation level 1, the 
   *  integer is the precedence *)
val parse_level1_pattern: #status -> int -> Ulexing.lexbuf -> NotationPt.term

  (** AST pattern: notation level 2 *)
val parse_level2_ast: #status -> Ulexing.lexbuf -> NotationPt.term
val parse_level2_meta: #status -> Ulexing.lexbuf -> NotationPt.term

(** {2 Grammar extension} *)

val check_l1_pattern: (* level1_pattern, pponly, precedence, assoc *)
 NotationPt.term -> bool ->  int -> Gramext.g_assoc -> checked_l1_pattern

val extend:
  #status as 'status -> 
  checked_l1_pattern ->
  (NotationEnv.t -> NotationPt.location -> NotationPt.term) ->
    'status

(** {2 Grammar entries}
 * needed by grafite parser *)

val level2_ast_grammar: #status -> Grammar.g

val term : #status -> NotationPt.term Grammar.Entry.e

val let_defs : #status ->
  (NotationPt.term NotationPt.capture_variable list * NotationPt.term NotationPt.capture_variable * NotationPt.term * int) list
    Grammar.Entry.e
val let_codefs : #status ->
  (NotationPt.term NotationPt.capture_variable list * NotationPt.term NotationPt.capture_variable * NotationPt.term * int) list
    Grammar.Entry.e

val protected_binder_vars : #status ->
  (NotationPt.term list * NotationPt.term option) Grammar.Entry.e

(** {2 Debugging} *)

  (** print "level2_pattern" entry on stdout, flushing afterwards *)
val print_l2_pattern: #status -> unit
