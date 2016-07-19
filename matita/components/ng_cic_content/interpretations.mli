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


  (** {2 State handling} *)

val hide_coercions: bool ref

type db

class type g_status =
  object
    inherit NCicCoercion.g_status
    method interp_db: db
  end

class virtual status :
  object ('self)
    inherit g_status
    inherit NCicCoercion.status
    method set_interp_db: db -> 'self
    method set_interp_status: #g_status -> 'self
  end

val add_interpretation:
  #status as 'status ->
  string ->                                       (* id / description *)
  string * NotationPt.argument_pattern list -> (* symbol, level 2 pattern *)
  NotationPt.cic_appl_pattern ->               (* level 3 pattern *)
    'status

exception Interpretation_not_found

  (** @raise Interpretation_not_found *)
val lookup_interpretations:
  #status ->
   ?sorted:bool -> string -> (* symbol *)
    (string * NotationPt.argument_pattern list *
      NotationPt.cic_appl_pattern) list

  (** {3 Interpretations toggling} *)

val toggle_active_interpretations: #status as 'status -> bool -> 'status

  (** {2 content -> cic} *)

  (** @param env environment from argument_pattern to cic terms
   * @param pat cic_appl_pattern *)
val instantiate_appl_pattern:
  mk_appl:('term list -> 'term) -> 
  mk_implicit:(bool -> 'term) ->
  term_of_nref : (NReference.reference -> 'term) ->
  (string * 'term) list -> NotationPt.cic_appl_pattern ->
    'term

val nmap_term:
 #status ->
  metasenv:NCic.metasenv -> subst:NCic.substitution -> context:NCic.context ->
  NCic.term ->
   NotationPt.term *
   (Content.id, NReference.reference) Hashtbl.t    (* id -> reference *)

val nmap_context:
 #status ->
  metasenv:NCic.metasenv -> subst:NCic.substitution ->
  NCic.context ->
   NotationPt.term Content.context *
   (Content.id, NReference.reference) Hashtbl.t    (* id -> reference *)

val nmap_sequent:
 #status -> metasenv:NCic.metasenv -> subst:NCic.substitution ->
  int * NCic.conjecture ->
   NotationPt.term Content.conjecture *
    (Content.id, NReference.reference) Hashtbl.t    (* id -> reference *)

val nmap_cobj:
 #status -> NCic.obj ->
  NotationPt.term Content.cobj *
   (Content.id, NReference.reference) Hashtbl.t    (* id -> reference *)

val nmap_obj:
 #status -> NCic.obj ->
  NotationPt.term NotationPt.obj *
   (Content.id, NReference.reference) Hashtbl.t    (* id -> reference *)
