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

(* $Id: xmlPushParser.ml 5769 2006-01-08 18:00:22Z sacerdot $ *)

let gzip_bufsize = 10240

type callbacks = {
  start_element: (string -> (string * string) list -> unit) option;
  end_element: (string -> unit) option;
  character_data: (string -> unit) option;
  processing_instruction: (string -> string -> unit) option;
  comment: (string -> unit) option;
}

let default_callbacks = {
  start_element = None;
  end_element = None;
  character_data = None;
  processing_instruction = None;
  comment = None;
}

type xml_source =
  [ `Channel of in_channel
  | `File of string
  | `Gzip_channel of Gzip.in_channel
  | `Gzip_file of string
  | `String of string
  ]

type position = int * int

type xml_parser = Expat.expat_parser

exception Parse_error of string

let create_parser callbacks =
  let expat_parser = Expat.parser_create ~encoding:None in
  (match callbacks.start_element with
  | Some f -> Expat.set_start_element_handler expat_parser f
  | _ -> ());
  (match callbacks.end_element with
  | Some f -> Expat.set_end_element_handler expat_parser f
  | _ -> ());
  (match callbacks.character_data with
  | Some f -> Expat.set_character_data_handler expat_parser f
  | _ -> ());
  (match callbacks.processing_instruction with
  | Some f -> Expat.set_processing_instruction_handler expat_parser f
  | _ -> ());
  (match callbacks.comment with
  | Some f -> Expat.set_comment_handler expat_parser f
  | _ -> ());
  expat_parser

let final = Expat.final

let get_position expat_parser =
  (Expat.get_current_line_number expat_parser,
   Expat.get_current_column_number expat_parser)

let parse expat_parser =
  let parse_fun = Expat.parse expat_parser in
  let rec aux = function
    | `Channel ic ->
        (try
          while true do parse_fun (input_line ic ^ "\n") done
        with End_of_file -> final expat_parser)
    | `File fname ->
        let ic = open_in fname in
        aux (`Channel ic);
        close_in ic
    | `Gzip_channel ic ->
        let buf = String.create gzip_bufsize in
        (try
          while true do
            let bytes = Gzip.input ic buf 0 gzip_bufsize in
            if bytes = 0 then raise End_of_file;
            parse_fun (String.sub buf 0 bytes)
          done
        with End_of_file -> final expat_parser)
    | `Gzip_file fname ->
        let ic = Gzip.open_in fname in
        aux (`Gzip_channel ic);
        Gzip.close_in ic
    | `String s -> parse_fun s
  in
  aux

let parse expat_parser xml_source =
  try
    parse expat_parser xml_source
  with Expat.Expat_error xml_error ->
    raise (Parse_error (Expat.xml_error_to_string xml_error))

