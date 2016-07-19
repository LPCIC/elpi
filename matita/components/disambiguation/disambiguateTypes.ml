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

(* $Id: disambiguateTypes.ml 12479 2013-02-01 13:47:25Z fguidi $ *)

type 'a expected_type = [ `XTNone       (* unknown *)
                        | `XTSome of 'a (* the given term *) 
		        | `XTSort       (* any sort *)
		        | `XTInd        (* any (co)inductive type *)
                        ]

type domain_item =
  | Id of string               (* literal *)
  | Symbol of string * int     (* literal, instance num *)
  | Num of int                 (* instance num *)

exception Invalid_choice of (Stdpp.location * string) Lazy.t

module OrderedDomain =
  struct
    type t = domain_item
    let compare = Pervasives.compare
  end

(* module Domain = Set.Make (OrderedDomain) *)
module Environment =
struct
  module Environment' = Map.Make (OrderedDomain)

  include Environment'

  let find k env =
   match k with
      Symbol (sym,n) ->
       (try find k env
        with Not_found -> find (Symbol (sym,0)) env)
    | Num n ->
       (try find k env
        with Not_found -> find (Num 0) env)
    | _ -> find k env

  let cons desc_of_alias k v env =
    try
      let current = find k env in
      let dsc = desc_of_alias v in
      add k (v :: (List.filter (fun x -> desc_of_alias x <> dsc) current)) env
    with Not_found ->
      add k [v] env
end

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

let string_of_domain_item = function
  | Id s -> Printf.sprintf "ID(%s)" s
  | Symbol (s, i) -> Printf.sprintf "SYMBOL(%s,%d)" s i
  | Num i -> Printf.sprintf "NUM(instance %d)" i
