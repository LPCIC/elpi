(* Copyright (C) 2004, HELM Team.
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

open DisambiguateTypes

(** {2 Choice registration low-level interface} *)

  (** raised by lookup_XXXX below *)
exception Choice_not_found of string Lazy.t

(** {2 Choices lookup}
 * for user defined aliases *)

  (** @param dsc description (1st component of codomain_item) *)
val nlookup_num_by_dsc: string -> NCic.term codomain_item

  (** @param symbol symbol as per AST
   * @param dsc description (1st component of codomain_item)
   *)
val lookup_symbol_by_dsc: 
  #Interpretations.status ->
  mk_appl: ('term list -> 'term) ->
  mk_implicit: (bool -> 'term) ->
  term_of_nref: (NReference.reference -> 'term) ->
  string -> string -> 'term codomain_item

val mk_choice:
  mk_appl: ('term list -> 'term) ->
  mk_implicit: (bool -> 'term) ->
  term_of_nref: (NReference.reference -> 'term) ->
  string * NotationPt.argument_pattern list *
  NotationPt.cic_appl_pattern ->
    'term codomain_item

