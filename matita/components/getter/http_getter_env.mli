(* Copyright (C) 2005, HELM Team.
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

open Http_getter_types

  (** {2 general information} *)

val version       : string        (* getter version *)

  (** {2 environment gathered data} *)
  (** all *_dir values are returned with trailing "/" *)

val cache_dir     : string lazy_t         (* cache root *)
val dtd_dir       : string option lazy_t  (* DTDs' root directory *)
val port          : int lazy_t            (* port on which getter listens *)
val dtd_base_urls : string list lazy_t    (* base URLs for document patching *)
val prefixes      : (string * (string * prefix_attr list)) list lazy_t
                                          (* prefix map uri -> url + attrs *)

  (* {2 derived data} *)

val host          : string lazy_t         (* host on which getter listens *)
val my_own_url    : string lazy_t         (* URL at which contact getter *)

  (* {2 misc} *)

val env_to_string : unit -> string  (* dump a textual representation of the
                                    current http_getter settings on an output
                                    channel *)

val get_dtd_dir : unit -> string

