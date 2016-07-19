(* Copyright (C) 2004, HELM Team.
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

exception Macro_not_found of string
exception Utf8_not_found of string

  (** @param macro name
     @return utf8 string *)
val expand: string -> string

  (** @param tex TeX like command (e.g. \forall, \lnot, ...)
   * @return unicode character corresponding to the command if it exists, or the
   * unchanged command if not *)
val unicode_of_tex: string -> string

  (** ... the other way round *)
val tex_of_unicode: string -> string list

val pp_table: unit -> (string * (string list)) list
