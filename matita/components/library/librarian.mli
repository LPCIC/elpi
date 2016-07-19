(* Copyright (C) 2004-2008, HELM Team.
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

exception NoRootFor of string
exception FileNotFound of string

(* make a relative path absolute *)
val absolutize: string -> string 

(* a root file is a text, line oriented, file containing pairs separated by
 * the '=' character. Example:
 *
 *  baseuri = cic:/foo/bar
 *  include_paths = ../baz ../../pippo
 *
 * spaces at the end/begin of the line and around '=' are ignored,
 * multiple spaces in the middle of an item are shrinked to one.
 *)
val load_root_file: string -> (string*string) list

(* baseuri_of_script ?(inc:REG[matita.includes]) fname 
 *   -> 
 * root, buri, fullpath, rootrelativepath
 * sample: baseuri_of_script a.ma -> /home/pippo/devel/, cic:/matita/a,
 * /home/pippo/devel/a.ma, a.ma *)
val baseuri_of_script: 
  include_paths:string list -> string -> string * string * string * string

(* given a baseuri and a file name (relative to its root)
 * returns a baseuri:
 *    mk_baseuri "cic:/matita" "nat/plus.ma" -> "cic:/matita/nat/plus"
 *)    
val mk_baseuri: string -> string -> string

(* finds all the roots files in the specified dir, roots are
 * text files, readable by the user named 'root'
 *)
val find_roots_in_dir: string -> string list

(* true if the argunent starts with a uri scheme prefix *)
val is_uri: string -> bool
