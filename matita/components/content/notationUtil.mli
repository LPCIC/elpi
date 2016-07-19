(* Copyright (C) 2004-2005, HELM Team.
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

val fresh_name: unit -> string

val variables_of_term: NotationPt.term -> NotationPt.pattern_variable list
val names_of_term: NotationPt.term -> string list

  (** extract all keywords (i.e. string literals) from a level 1 pattern *)
val keywords_of_term: NotationPt.term -> string list

val visit_ast:
  ?special_k:(NotationPt.term -> NotationPt.term) ->
  ?map_xref_option:(NotationPt.href option -> NotationPt.href option) ->
  ?map_case_indty:(NotationPt.case_indtype option ->
          NotationPt.case_indtype option) ->
  ?map_case_outtype:((NotationPt.term -> NotationPt.term) -> 
                     NotationPt.term option -> NotationPt.term
  option) ->
  (NotationPt.term -> NotationPt.term) ->
  NotationPt.term ->
    NotationPt.term

val visit_layout:
  (NotationPt.term -> NotationPt.term) ->
  NotationPt.layout_pattern ->
    NotationPt.layout_pattern

val visit_magic:
  (NotationPt.term -> NotationPt.term) ->
  NotationPt.magic_term ->
    NotationPt.magic_term

val visit_variable:
  (NotationPt.term -> NotationPt.term) ->
  NotationPt.pattern_variable ->
    NotationPt.pattern_variable

val strip_attributes: NotationPt.term -> NotationPt.term

  (** @return the list of proper (i.e. non recursive) IdRef of a term *)
val get_idrefs: NotationPt.term -> string list

  (** generalization of List.combine to n lists *)
val ncombine: 'a list list -> 'a list list

val string_of_literal: NotationPt.literal -> string

val dress:  sep:'a -> 'a list -> 'a list
val dressn: sep:'a list -> 'a list -> 'a list

val boxify: NotationPt.term list -> NotationPt.term
val group: NotationPt.term list -> NotationPt.term
val ungroup: NotationPt.term list -> NotationPt.term list

val find_appl_pattern_uris:
  NotationPt.cic_appl_pattern -> NReference.reference list

val find_branch:
  NotationPt.term -> NotationPt.term

  (** Symbol/Numbers instances *)

val freshen_term: NotationPt.term -> NotationPt.term
val freshen_obj: NotationPt.term NotationPt.obj -> NotationPt.term NotationPt.obj

  (** Notation id handling *)

type notation_id

val fresh_id: unit -> notation_id

val refresh_uri_in_term:
 refresh_uri_in_term:(NCic.term -> NCic.term) ->
 refresh_uri_in_reference:(NReference.reference -> NReference.reference) ->
  NotationPt.term -> NotationPt.term
