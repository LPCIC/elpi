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

(* Tokens for XML cdata, empty elements and not-empty elements           *)
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

(* currified versions of the token constructors make the code more readable *)
val xml_empty :
 ?prefix:string -> string -> (string option * string * string) list ->
   token Stream.t
val xml_nempty :
 ?prefix:string -> string -> (string option * string * string) list ->
   token Stream.t -> token Stream.t
val xml_cdata : string -> token Stream.t

(* The pretty printer for streams of token                                  *)
(* Usage:                                                                   *)
(*  pp tokens None     pretty prints the output on stdout                   *)
(*  pp tokens (Some filename) pretty prints the output on the file filename
* @param gzip if set to true files are gzipped. Defaults to false *)
val pp : ?gzip:bool -> token Stream.t -> string option -> unit
val pp_to_outchan : token Stream.t -> out_channel -> unit
val pp_to_string : token Stream.t -> string

val add_xml_declaration: token Stream.t -> token Stream.t

val strip_xml_headings: string -> string

