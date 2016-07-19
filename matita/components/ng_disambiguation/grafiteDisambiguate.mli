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

type db

class type g_status =
 object
  inherit Interpretations.g_status
  method disambiguate_db: db
 end

class virtual status :
 object ('self)
  inherit g_status
  inherit Interpretations.status
  method set_disambiguate_db: db -> 'self
  method set_disambiguate_status: #g_status -> 'self
 end

val eval_with_new_aliases:
 #status as 'status -> ('status -> 'a) ->
  (DisambiguateTypes.domain_item * GrafiteAst.alias_spec) list * 'a

val set_proof_aliases:
 #status as 'status ->
  implicit_aliases:bool -> (* implicit ones are made explicit *)
  GrafiteAst.inclusion_mode ->
  (DisambiguateTypes.domain_item * GrafiteAst.alias_spec) list -> 'status

val aliases_for_objs:
 #NCic.status -> NUri.uri list ->
  (DisambiguateTypes.domain_item * GrafiteAst.alias_spec) list

(* args: print function, message (may be empty), status *) 
val dump_aliases: (string -> unit) -> string -> #status -> unit

exception BaseUriNotSetYet

val disambiguate_nterm :
 #status as 'status ->
 NCic.term NCicRefiner.expected_type -> NCic.context -> NCic.metasenv -> NCic.substitution ->
 NotationPt.term Disambiguate.disambiguator_input ->
   NCic.metasenv * NCic.substitution * 'status * NCic.term

val disambiguate_nobj :
 #status as 'status -> ?baseuri:string ->
 (NotationPt.term NotationPt.obj) Disambiguate.disambiguator_input ->
  'status * NCic.obj

type pattern = 
  NotationPt.term Disambiguate.disambiguator_input option * 
  (string * NCic.term) list * NCic.term option

val disambiguate_npattern:
 #NCic.status -> GrafiteAst.npattern Disambiguate.disambiguator_input -> pattern

val disambiguate_cic_appl_pattern:
 #status ->
  NotationPt.argument_pattern list ->
   NotationPt.cic_appl_pattern -> NotationPt.cic_appl_pattern
