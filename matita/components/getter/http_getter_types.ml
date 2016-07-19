(*
 * Copyright (C) 2003-2004:
 *    Stefano Zacchiroli <zack@cs.unibo.it>
 *    for the HELM Team http://helm.cs.unibo.it/
 *
 *  This file is part of HELM, an Hypertextual, Electronic
 *  Library of Mathematics, developed at the Computer Science
 *  Department, University of Bologna, Italy.
 *
 *  HELM is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License
 *  as published by the Free Software Foundation; either version 2
 *  of the License, or (at your option) any later version.
 *
 *  HELM is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with HELM; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 *  MA  02111-1307, USA.
 *
 *  For details, see the HELM World-Wide-Web page,
 *  http://helm.cs.unibo.it/
 *)

(* $Id: http_getter_types.ml 5788 2006-01-09 13:50:58Z zacchiro $ *)

exception Bad_request of string
exception Unresolvable_URI of string
exception Invalid_URI of string
exception Invalid_URL of string
exception Invalid_RDF_class of string
exception Internal_error of string
exception Cache_failure of string
exception Dtd_not_found of string (* dtd's url *)
exception Key_already_in of string;;
exception Key_not_found of string;;
exception Http_client_error of string * string  (* url, error message *)
exception Unsupported_scheme of string  (** unsupported url scheme *)

type encoding = [ `Normal | `Gzipped ]
type answer_format = [ `Text | `Xml ]
type ls_flag = No | Yes | Ann
type ls_object =
  {
    uri: string;
    ann: bool;
    types: ls_flag;
    body: ls_flag;
    proof_tree: ls_flag;
  }
type ls_item =
  | Ls_section of string
  | Ls_object of ls_object

type xml_uri =
  | Cic of string
  | Theory of string
type rdf_uri = string * xml_uri
type nuprl_uri = string
type uri =
  | Cic_uri of xml_uri
  | Nuprl_uri of nuprl_uri
  | Rdf_uri of rdf_uri

module StringSet = Set.Make (String)

type prefix_attr = [ `Read_only | `Legacy ]

