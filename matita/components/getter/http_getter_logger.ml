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

(* $Id: http_getter_logger.ml 5769 2006-01-08 18:00:22Z sacerdot $ *)

let log_level = ref 1
let get_log_level () = !log_level
let set_log_level l = log_level := l

(* invariant: if logfile is set, then logchan is set too *)
let logfile = ref None
let logchan = ref None

let set_log_file f =
  (match !logchan with None -> () | Some oc -> close_out oc);
  match f with
  | Some f ->
      logfile := Some f;
      logchan := Some (open_out f)
  | None ->
      logfile := None;
      logchan := None

let get_log_file () = !logfile

let close_log_file () = set_log_file None

let log ?(level = 1) s =
  if level <= !log_level then
    let msg = "[HTTP-Getter] " ^ s in
    match (!logfile, !logchan) with
    | None, _ -> prerr_endline msg
    | Some fname, Some oc ->
        output_string oc msg;
        output_string oc "\n";
        flush oc
    | Some _, None -> assert false

