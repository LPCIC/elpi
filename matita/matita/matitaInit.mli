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

  (** {2 global initialization} *)
val initialize_all: unit -> unit

  (** {2 per-components initialization} *)
val parse_cmdline_and_configuration_file: unit -> unit
val initialize_environment: unit -> unit

  (** {2 Utilities} *)

  (** die nicely: exit with return code 1 printing usage error message *)
val die_usage: unit -> 'a

  (** add extra command line options *)
val add_cmdline_spec: (Arg.key * Arg.spec * Arg.doc) list -> unit

