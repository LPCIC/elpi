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

open Http_getter_types;;

val string_of_ls_flag: ls_flag -> string
val string_of_encoding: encoding -> string

val is_cic_uri: string -> bool
val is_cic_obj_uri: string -> bool
val is_theory_uri: string -> bool
val is_nuprl_uri: string -> bool
val is_rdf_uri: string -> bool
val is_xsl_uri: string -> bool

val uri_of_string: string -> uri

  (** @param xmlbases (xml base URI * xml base URL) *)
val patch_xml :
  ?via_http:bool -> ?xmlbases:(string * string) -> unit -> (string -> string)
val patch_dtd : ?via_http:bool -> unit -> (string -> string)
  (* TODO via_http not yet supported for patch_xsl *)
val patch_xsl : ?via_http:bool -> unit -> (string -> string)

  (**
  @param fname name of the file to be sent
  @param contype Content-Type header value
  @param contenc Content-Enconding header value
  @param patch_fun function used to patch file contents
  @param gunzip is meaningful only if a patch function is provided. If gunzip
  is true and patch_fun is given (i.e. is not None), then patch_fun is applied
  to the uncompressed version of the file. The file is then compressed again and
  send to client
  @param via_http (default: true) if true http specific communications are used
  (e.g. headers, crlf before body) and sent via outchan, otherwise they're not.
  Set it to false when saving to a local file
  @param outchan output channel over which sent file fname *)
val return_file:
  fname:string ->
  ?contype:string -> ?contenc:string ->
  ?patch_fun:(string -> string) -> ?gunzip:bool -> ?via_http:bool ->
  enc:encoding ->
  out_channel ->
    unit

