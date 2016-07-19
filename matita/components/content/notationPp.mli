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

(** ZACK
 * This module does not print terms and object properly, it has been created
 * mainly for debugging reason. There is no guarantee that printed strings are
 * re-parsable. Moreover, actually there is no way at all to proper print
 * objects in a way that is re-parsable.
 *
 * TODO the proper implementation of a pp_obj function like the one below should
 * be as follows. Change its type to
 *  pp_obj: NotationPt.obj -> NotationPres.markup
 * and parametrize it over a function with the following type
 *  pp_term: NotationPt.term -> NotationPres.markup
 * The obtained markup can then be printed using CicNotationPres.print_xml or
 * BoxPp.render_to_string(s)
 *)

val pp_term: #NCic.status -> NotationPt.term -> string
val pp_obj: ('term -> string) -> 'term NotationPt.obj -> string

val pp_env: #NCic.status -> NotationEnv.t -> string
val pp_value: #NCic.status -> NotationEnv.value -> string
val pp_value_type: NotationEnv.value_type -> string

val pp_pos: NotationPt.child_pos -> string
val pp_attribute: NotationPt.term_attribute -> string

val pp_cic_appl_pattern: NotationPt.cic_appl_pattern -> string

 (** non re-entrant change of pp_term function above *)
val set_pp_term: (NCic.status -> NotationPt.term -> string) -> unit
