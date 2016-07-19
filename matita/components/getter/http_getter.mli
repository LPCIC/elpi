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

open Http_getter_types

  (** {2 Loggers} *)

type logger_callback = HelmLogger.html_tag -> unit

val stdout_logger: logger_callback

  (** {2 Getter Web Service interface as API *)

val help: unit -> string

  (** @raise Http_getter_types.Unresolvable_URI _
  * @raise Http_getter_types.Key_not_found _ *)
val resolve: local:bool -> writable:bool -> string -> string (* uri -> url *)

  (** as resolve, but does not check if the resource exists
   * @raise Http_getter_types.Key_not_found *)
val filename: local:bool -> writable:bool -> string -> string (* uri -> url *)

val exists: local:bool -> string -> bool

val getxml  : string -> string
val getxslt : string -> string
val getdtd  : string -> string
val clean_cache: unit -> unit
val getalluris: unit -> string list

  (** @param baseuri uri to be listed, simple form or regular expressions (a
   * single choice among parens) are permitted *)
val ls: local:bool -> string -> ls_item list

  (** {2 UriManager shorthands} *)

val getxml'     : NUri.uri -> string
val resolve'    : local:bool -> writable:bool -> NUri.uri -> string
val exists'     : local:bool -> NUri.uri -> bool
val filename'     : local:bool -> writable:bool -> NUri.uri -> string

  (** {2 Misc} *)

val init: unit -> unit

