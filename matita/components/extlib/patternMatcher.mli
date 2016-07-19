
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

type pattern_kind = Variable | Constructor
type tag_t = int

module type PATTERN =
sig
  type pattern_t
  type term_t

  val classify : pattern_t -> pattern_kind
  val tag_of_pattern : pattern_t -> tag_t * pattern_t list
  val tag_of_term : term_t -> tag_t * term_t list

  (** {3 Debugging} *)
  val string_of_term: term_t -> string
  val string_of_pattern: pattern_t -> string
end

module Matcher (P: PATTERN) :
sig
  (** @param patterns pattern matrix (pairs <pattern, pattern_id>)
   * @param success_cb callback invoked in case of matching.
   *  Its argument are the list of pattern who matches the input term, the list
   *  of terms bound in them, the list of terms which matched constructors.
   *  Its return value is Some _ if the matching is valid, None otherwise; the
   *  latter kind of return value will trigger backtracking in the pattern
   *  matching algorithm
   * @param failure_cb callback invoked in case of matching failure
   * @param term term on which pattern match on *)
  val compiler:
    (P.pattern_t * int) list ->
    ((P.pattern_t list * int) list -> P.term_t list -> P.term_t list ->
      'a option) ->                   (* terms *)    (* constructors *)
    (unit -> 'a option) ->
      (P.term_t -> 'a option)
end

