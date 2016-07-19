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

val debug: bool ref

(* the integer is an offset to be added to each location *)
exception DisambiguationError of
 int *
 ((Stdpp.location list * string * string) list *
  (DisambiguateTypes.domain_item * string) list *
  (Stdpp.location * string) Lazy.t * bool) list list
  (** parameters are: option name, error message *)

(** initially false; for debugging only (???) *)
val only_one_pass: bool ref
val use_library: bool ref

val passes : unit -> (bool * [> `Library | `Mono | `Multi ] * bool) list

val disambiguate_thing:
  passes:(bool * [ `Library | `Mono | `Multi ] * bool) list ->
  freshen_thing: ('ast_thing -> 'ast_thing) ->
  context:'context ->
  metasenv:'metasenv ->
  subst:'subst ->
  string_context_of_context:('context -> string option list) ->
  initial_ugraph:'ugraph ->
  expty: 'refined_thing DisambiguateTypes.expected_type ->
  mk_implicit:(bool -> 'alias) ->
  description_of_alias:('alias -> string) ->
  fix_instance:(DisambiguateTypes.domain_item -> 'alias list -> 'alias list) ->
  aliases:'alias DisambiguateTypes.Environment.t ->
  universe:'alias list
    DisambiguateTypes.Environment.t option ->
  lookup_in_library:(
    DisambiguateTypes.interactive_user_uri_choice_type ->
    DisambiguateTypes.input_or_locate_uri_type ->
    DisambiguateTypes.Environment.key ->
    'alias list) ->
  uri:'uri ->
  pp_thing:('ast_thing -> string) ->
  domain_of_thing:
   (context: string option list -> 'ast_thing -> Disambiguate.domain) ->
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
      ('refined_thing, 'metasenv,'subst,'ugraph) Disambiguate.test_result) ->
  mk_localization_tbl:(int -> 'cichash) ->
  string * int * 'ast_thing ->
  ((DisambiguateTypes.Environment.key * 'alias) list * 
   'metasenv * 'subst * 'refined_thing * 'ugraph)
  list * bool
