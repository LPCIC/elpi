(* Copyright (C) 2000, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

(******************************************************************************)
(*                                                                            *)
(*                               PROJECT HELM                                 *)
(*                                                                            *)
(*                     A tactic to print Coq objects in XML                   *)
(*                                                                            *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                 18/10/2000                                 *)
(*                                                                            *)
(* This module defines a pretty-printer and the stream of commands to the pp  *)
(*                                                                            *)
(******************************************************************************)

(* $Id: xml.ml 7703 2007-09-23 12:27:52Z fguidi $ *)


(* the type token for XML cdata, empty elements and not-empty elements *)
(* Usage:                                                             *)
(*  Str cdata                                                         *)
(*  Empty (prefix, element_name,                                      *)
(*   [prefix1, attrname1, value1 ; ... ; prefixn, attrnamen, valuen]  *)
(*  NEmpty (prefix, element_name,                                     *)
(*   [prefix1, attrname1, value1 ; ... ; prefixn, attrnamen, valuen], *)
(*    content                                                         *)
type token =
   Str of string
 | Empty of string option * string * (string option * string * string) list
 | NEmpty of string option * string * (string option * string * string) list *
    token Stream.t
;;

(* currified versions of the constructors make the code more readable *)
let xml_empty ?prefix name attrs =
 [< 'Empty(prefix,name,attrs) >]
let xml_nempty ?prefix name attrs content =
 [< 'NEmpty(prefix,name,attrs,content) >]
let xml_cdata str =
 [< 'Str str >]

(** low level for other PPs: pretty print each token of strm applying 'f' to a
canonical string representation of each token *)
let pp_gen f strm =
 let pprefix =
  function
     None -> ""
   | Some p -> p ^ ":" in
 let rec pp_r m =
  parser
  | [< 'Str a ; s >] ->
      print_spaces m ;
      f (a ^ "\n") ;
      pp_r m s
  | [< 'Empty(p,n,l) ; s >] ->
      print_spaces m ;
      f ("<" ^ (pprefix p) ^ n) ;
      List.iter (fun (p,n,v) -> f (" " ^ (pprefix p) ^ n ^ "=\"" ^ v ^ "\"")) l;
      f "/>\n" ;
      pp_r m s
  | [< 'NEmpty(p,n,l,c) ; s >] ->
      print_spaces m ;
      f ("<" ^ (pprefix p) ^ n) ;
      List.iter (fun (p,n,v) -> f (" " ^ (pprefix p) ^ n ^ "=\"" ^ v ^ "\"")) l;
      f ">\n" ;
      pp_r (m+1) c ;
      print_spaces m ;
      f ("</" ^ (pprefix p) ^ n ^ ">\n") ;
      pp_r m s
  | [< >] -> ()
 and print_spaces m =
  for i = 1 to m do f "  " done
 in
 pp_r 0 strm
;;

(** pretty printer on output channels *)
let pp_to_outchan strm oc =
  pp_gen (fun s -> output_string oc s) strm;
  flush oc
;;

let pp_to_gzipchan strm oc =
  pp_gen (fun s -> Gzip.output oc s 0 (String.length s)) strm
;;

(** pretty printer to string *)
let pp_to_string strm =
  let buf = Buffer.create 10240 in
  pp_gen (Buffer.add_string buf) strm;
  Buffer.contents buf
;;

(** pretty printer to file *)
(* Usage:                                                                   *)
(*  pp tokens None     pretty prints the output on stdout                   *)
(*  pp tokens (Some filename) pretty prints the output on the file filename *)
let pp ?(gzip=false) strm fn =
  if gzip then
    match fn with
    | Some filename ->
        let outchan = Gzip.open_out filename in
        begin try
          pp_to_gzipchan strm outchan;
        with e ->
          Gzip.close_out outchan;
          raise e
	end;
        Gzip.close_out outchan;
	HExtlib.chmod 0o664 filename;
    | None -> failwith "Can't sent gzipped output to stdout"
  else
    match fn with
    | Some filename ->
        let outchan = open_out filename in
        begin try
          pp_to_outchan strm outchan;
        with e ->
          close_out outchan;
          raise e
	end;
        close_out outchan;
	HExtlib.chmod 0o664 filename
    | None -> pp_to_outchan strm stdout
;;

let pp =
 let profiler = HExtlib.profile "Xml.pp" in
  fun ?gzip strm fn ->
   profiler.HExtlib.profile (pp ?gzip strm) fn
;;

let add_xml_declaration stream =
  let box_prefix = "b" in
  [<
    xml_cdata "<?xml version=\"1.0\" ?>\n" ;
    xml_cdata "\n";
    xml_nempty ~prefix:box_prefix "box"
      [ Some "xmlns","m","http://www.w3.org/1998/Math/MathML" ;
        Some "xmlns","b","http://helm.cs.unibo.it/2003/BoxML" ;
        Some "xmlns","helm","http://www.cs.unibo.it/helm" ;
        Some "xmlns","xlink","http://www.w3.org/1999/xlink"
      ] stream
  >]

  (* TODO BRRRRR .... *)
  (** strip first 4 line of a string, used to strip xml declaration and doctype
  declaration from XML strings generated by Xml.pp_to_string *)
let strip_xml_headings s =
  let rec aux n pos =
    if n = 0
    then String.sub s pos (String.length s - pos)
    else aux (n - 1) (String.index_from s pos '\n' + 1)
  in
  try
    aux 4 0
  with Not_found -> s

