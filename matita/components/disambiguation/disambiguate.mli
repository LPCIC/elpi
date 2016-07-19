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

(** {2 Disambiguation interface} *)

(** raised when ambiguous input is found but not expected (e.g. in the batch
  * compiler) *)
exception Ambiguous_input

(* the integer is an offset to be added to each location *)
(* list of located error messages, each list is a tuple:
  * - environment in string form
  * - environment patch
  * - location
  * - error message
  * - significancy of the error message, if false the error is likely to be
  *   useless for the final user ... *)
exception NoWellTypedInterpretation of
 int *
 ((Stdpp.location list * string * string) list *
  (DisambiguateTypes.domain_item * string) list *
  (Stdpp.location * string) Lazy.t *
  bool) list
exception PathNotWellFormed

type 'a disambiguator_input = string * int * 'a
    
type domain = domain_tree list
and domain_tree = 
  Node of Stdpp.location list * DisambiguateTypes.domain_item * domain

type ('term,'metasenv,'subst,'graph) test_result =
  | Ok of 'term * 'metasenv * 'subst * 'graph
  | Ko of (Stdpp.location * string) Lazy.t
  | Uncertain of (Stdpp.location * string) Lazy.t

exception Try_again of string Lazy.t

val set_choose_uris_callback:
  DisambiguateTypes.interactive_user_uri_choice_type -> unit

val set_choose_interp_callback:
  DisambiguateTypes.interactive_interpretation_choice_type -> unit

(** @raise Ambiguous_input if called, default value for internal
  * choose_uris_callback if not set otherwise with set_choose_uris_callback
  * above *)
val mono_uris_callback: DisambiguateTypes.interactive_user_uri_choice_type

(** @raise Ambiguous_input if called, default value for internal
  * choose_interp_callback if not set otherwise with set_choose_interp_callback
  * above *)
val mono_interp_callback: DisambiguateTypes.interactive_interpretation_choice_type

val resolve : 
  env:'alias DisambiguateTypes.Environment.t ->
  mk_choice:('alias -> 'term DisambiguateTypes.codomain_item) ->
  DisambiguateTypes.Environment.key ->
   [`Num_arg of string | `Args of 'term list] -> 'term

val find_in_context: string -> string option list -> int
val domain_of_term: context:
  string option list -> NotationPt.term -> domain
val domain_of_obj: 
  context:string option list -> NotationPt.term NotationPt.obj -> domain

val disambiguate_thing:
  context:'context ->
  metasenv:'metasenv ->
  subst:'subst ->
  use_coercions:bool ->
  string_context_of_context:('context -> string option list) ->
  initial_ugraph:'ugraph ->
  expty: 'refined_thing DisambiguateTypes.expected_type ->
  mk_implicit:(bool -> 'alias) ->
  description_of_alias:('alias -> string) ->
  fix_instance:(DisambiguateTypes.domain_item -> 'alias list -> 'alias list) ->
  aliases:'alias DisambiguateTypes.Environment.t ->
  universe:'alias list DisambiguateTypes.Environment.t option ->
  lookup_in_library:(
    DisambiguateTypes.interactive_user_uri_choice_type ->
    DisambiguateTypes.input_or_locate_uri_type ->
    DisambiguateTypes.Environment.key ->
    'alias list) ->
  uri:'uri ->
  pp_thing:('ast_thing -> string) ->
  domain_of_thing:(context: string option list -> 'ast_thing -> domain) ->
  interpretate_thing:(
    context:'context ->
    env:'alias DisambiguateTypes.Environment.t ->
    uri:'uri ->
    is_path:bool -> 
    'ast_thing -> 
    localization_tbl:'cichash -> 
      'raw_thing) ->
  refine_thing:(
    'metasenv -> 'subst -> 'context -> 'uri -> use_coercions:bool ->
    'raw_thing -> 'refined_thing DisambiguateTypes.expected_type -> 'ugraph -> localization_tbl:'cichash -> 
      ('refined_thing, 'metasenv,'subst,'ugraph) test_result) ->
  mk_localization_tbl:(int -> 'cichash) ->
  'ast_thing disambiguator_input ->
  ((DisambiguateTypes.Environment.key * 'alias) list * 
   'metasenv * 'subst * 'refined_thing * 'ugraph)
  list * bool

