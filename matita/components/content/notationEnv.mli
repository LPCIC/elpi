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

(** {2 Types} *)

type ident_or_var =
   Ident of string
 | Var of string

type value =
  | TermValue of NotationPt.term
  | StringValue of ident_or_var
  | NumValue of string
  | OptValue of value option
  | ListValue of value list

type value_type =
  | TermType of int (* the level of the expected term *)
  | StringType
  | NumType
  | OptType of value_type
  | ListType of value_type

  (** looked up value not found in environment *)
exception Value_not_found of string

  (** looked up value has the wrong type
   * parameters are value name and value type in environment *)
exception Type_mismatch of string * value_type

type declaration = string * value_type
type binding = string * (value_type * value)
type t = binding list

val declaration_of_var: NotationPt.pattern_variable -> declaration
val value_of_term: NotationPt.term -> value
val term_of_value: value -> NotationPt.term
val well_typed: value_type -> value -> bool

val declarations_of_env: t -> declaration list
val declarations_of_term: NotationPt.term -> declaration list
val combine: declaration list -> value list -> t  (** @raise Invalid_argument *)

(** {2 Environment lookup} *)

val lookup_value:   t -> string -> value  (** @raise Value_not_found *)

(** lookup_* functions below may raise Value_not_found and Type_mismatch *)

val lookup_term:    t -> string -> NotationPt.term
val lookup_string:  t -> string -> ident_or_var
val lookup_num:     t -> string -> string
val lookup_opt:     t -> string -> value option
val lookup_list:    t -> string -> value list

val remove_name:    t -> string -> t
val remove_names:   t -> string list -> t

(** {2 Bindings mangling} *)

val opt_binding_some: binding -> binding          (* v -> Some v *)
val opt_binding_none: binding -> binding          (* v -> None *)

val opt_binding_of_name:  declaration -> binding  (* None binding *)
val list_binding_of_name: declaration -> binding  (* [] binding *)

val opt_declaration:  declaration -> declaration  (* t -> OptType t *)
val list_declaration: declaration -> declaration  (* t -> ListType t *)

(** given a list of environments bindings a set of names n_1, ..., n_k, returns
 * a single environment where n_i is bound to the list of values bound in the
 * starting environments *)
val coalesce_env: declaration list -> t list -> t

