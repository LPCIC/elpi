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

(** {2 XLM push parser generic interface}
 * Do not depend on CIC *)

  (** callbacks needed to instantiate a parser *)
type callbacks = {
  start_element:
    (string -> (string * string) list -> unit) option;  (* tag, attr list *)
  end_element: (string -> unit) option;                 (* tag *)
  character_data: (string -> unit) option;              (* data *)
  processing_instruction:
    (string -> string -> unit) option;                  (* target, value *)
  comment: (string -> unit) option;                     (* value *)
}

  (** do nothing callbacks (all set to None) *)
val default_callbacks: callbacks

  (** source from which parse an XML file *)
type xml_source =
  [ `Channel of in_channel
  | `File of string
  | `Gzip_channel of Gzip.in_channel
  | `Gzip_file of string
  | `String of string
  ]

  (** source position in a XML source.
   * A position is a pair <line, column> *)
type position = int * int

type xml_parser

  (** raised when a parse error occurs, argument is an error message.
   * This exception carries no position information, but it should be get using
   * get_position below *)
exception Parse_error of string

  (** Create a push parser which invokes the given callbacks *)
val create_parser: callbacks -> xml_parser

  (** Parse XML data from a given source with a given parser
    * @raise Parse_error *)
val parse: xml_parser -> xml_source -> unit

  (** Inform the parser that parsing is completed, needed only when source is
   * `String, for other sources it is automatically invoked when the end of file
   * is reached
   * @raise Parse_error *)
val final: xml_parser -> unit

  (** @return current <line, column> pair *)
val get_position: xml_parser -> position

