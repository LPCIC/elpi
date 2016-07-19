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

(** Transparent handling of local/remote getter resources.
 * Configuration of this module are prefix mappings (see
 * Http_getter_env.prefixes). All functions of this module take as input an URI,
 * resolve it using mappings and act on the resulting resource which can be
 * local (file:/// scheme or relative path) or remote via HTTP (http:// scheme).
 *
 * Each resource could be either compressed (trailing ".gz") or non-compressed.
 * All functions of this module will first loook for the compressed resource
 * (i.e. the asked one ^ ".gz"), falling back to the non-compressed one.
 *
 * All filenames returned by functions of this module exists on the filesystem
 * after function's return.
 *
 * Almost all functions may raise Resource_not_found, the following invariant
 * holds: that exception is raised iff exists return false on a given resource
 * *)

exception Resource_not_found of string * string  (** method, uri *)

  (** @return a list of string where dir are returned with a trailing "/" *)
val ls: local:bool -> string -> string list


  (** @return the filename of the resource corresponding to a given uri. Handle
   * download and caching for remote resources.
   * @param find if set to true all matching prefixes will be searched for the
   * asked resource, if not only the best matching prefix will be used. Note
   * that the search is performed only if the asked resource is not found in
   * cache (i.e. to perform the find again you need to clean the cache).
   * Defaults to false *)
val filename: local:bool -> ?find:bool -> string -> string

  (** only works for local resources
   * if both compressed and non-compressed versions of a resource exist, both of
   * them are removed *)
val remove: string -> unit

val exists: local:bool -> string -> bool
val resolve: 
  local:bool -> ?must_exists:bool -> writable:bool -> string -> string

(* val get_attrs: string -> Http_getter_types.prefix_attr list *)
val is_read_only: string -> bool
val is_legacy: string -> bool
val is_empty: local:bool -> string -> bool

val clean_cache: unit -> unit

val activate_system_mode: unit -> unit
val list_writable_prefixes: unit -> string list
