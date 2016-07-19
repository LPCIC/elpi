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

(* $Id: hLog.ml 5769 2006-01-08 18:00:22Z sacerdot $ *)

open Printf

type log_tag = [ `Debug | `Error | `Message | `Warning ]
type log_callback = log_tag -> string -> unit

(* 
colors=(black red green yellow blue magenta cyan gray white)
ccodes=(30 31 32 33 34 35 36 37 39)
*)

let blue   = "[0;34m"
let yellow = "[0;33m"
let green  = "[0;32m"
let red    = "[0;31m"
let black  = "[0m"

let default_callback tag s =
  let prefix,ch =
    match tag with
    | `Message -> green  ^ "Info:  ", stdout
    | `Warning -> yellow ^ "Warn:  ", stderr
    | `Error ->   red    ^ "Error: ", stderr
    | `Debug ->   blue   ^ "Debug: ", stderr
  in
  output_string ch (prefix ^ black ^ s ^ "\n");
  flush ch

let callback = ref default_callback

let set_log_callback f = callback := f
let get_log_callback () = !callback

let message s = !callback `Message s
let warn s = !callback `Warning s
let error s = !callback `Error s
let debug s = !callback `Debug s

