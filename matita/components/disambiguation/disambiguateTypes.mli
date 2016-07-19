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

type 'a expected_type = [ `XTNone       (* unknown *)
                        | `XTSome of 'a (* the given term *) 
		        | `XTSort       (* any sort *)
		        | `XTInd        (* any (co)inductive type *)
                        ]

type domain_item =
 | Id of string               (* literal *)
 | Symbol of string * int     (* literal, instance num *)
 | Num of int                 (* instance num *)

(* module Domain:      Set.S with type elt = domain_item *)
module Environment:
sig
  include Map.S with type key = domain_item
  val cons: ('b -> 'a) -> domain_item -> 'b -> 'b list t -> 'b list t
end

  (** to be raised when a choice is invalid due to some given parameter (e.g.
   * wrong number of Cic.term arguments received) *)
exception Invalid_choice of (Stdpp.location * string) Lazy.t

type 'term codomain_item =
  string *  (* description *)
   [`Num_interp of string -> 'term
   |`Sym_interp of 'term list -> 'term]

type interactive_user_uri_choice_type =
  selection_mode:[`SINGLE | `MULTIPLE] ->
  ?ok:string ->
  ?enable_button_for_non_vars:bool ->
  title:string -> msg:string -> id:string -> NReference.reference list ->
   NReference.reference list

type interactive_interpretation_choice_type = string -> int ->
  (Stdpp.location list * string * string) list list -> int list

type input_or_locate_uri_type = 
  title:string -> ?id:string -> unit -> NReference.reference option

val string_of_domain_item: domain_item -> string
