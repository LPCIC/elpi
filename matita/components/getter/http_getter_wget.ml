(* Copyright (C) 2000-2005, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

(* $Id: http_getter_wget.ml 10360 2009-09-30 13:35:06Z ricciott $ *)

open Http_getter_types

let send cmd =
  try
    ignore (Http_user_agent.get cmd)
  with exn -> raise (Http_client_error (cmd, Printexc.to_string exn))

let get url =
  try
    Http_user_agent.get url
  with exn -> raise (Http_client_error (Printexc.to_string exn, url))

let get_and_save url dest_filename =
  let out_channel = open_out dest_filename in
  (try
    Http_user_agent.get_iter (output_string out_channel) url;
  with exn ->
    close_out out_channel;
    Sys.remove dest_filename;
    raise (Http_client_error (Printexc.to_string exn, url)));
  close_out out_channel

let get_and_save_to_tmp url =
  let flat_string s s' c =
    let cs = String.copy s in
    for i = 0 to (String.length s) - 1 do
      if String.contains s' s.[i] then cs.[i] <- c
    done;
    cs
  in
  let user = try Unix.getlogin () with _ -> "" in
  let tmp_file =
    Filename.temp_file (user ^ flat_string url ".-=:;!?/&" '_') ""
  in
  get_and_save url tmp_file;
  tmp_file

let exists url =
  try
    ignore (Http_user_agent.head url);
    true
  with
     Http_user_agent.Http_error _ -> false
   | Not_found -> prerr_endline (Printf.sprintf "An object %s has metadata but no XML. This is an internal bug of ocaml-http: Zack, please fix it!" 
                  url); assert false

