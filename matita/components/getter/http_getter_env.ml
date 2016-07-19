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

(* $Id: http_getter_env.ml 6371 2006-05-29 14:12:40Z sacerdot $ *)

open Printf

open Http_getter_types
open Http_getter_misc

let version = Http_getter_const.version

let prefix_RE = Pcre.regexp "^\\s*([^\\s]+)\\s+([^\\s]+)\\s*(.*)$"

let cache_dir  = lazy (normalize_dir (Helm_registry.get "getter.cache_dir"))
let dtd_dir = lazy (
  match Helm_registry.get_opt Helm_registry.string "getter.dtd_dir" with
  | None -> None
  | Some dir -> Some (normalize_dir dir))
let dtd_base_urls  = lazy (
  let rex = Pcre.regexp "/*$" in
  let raw_urls =
    match
      Helm_registry.get_list Helm_registry.string "getter.dtd_base_urls"
    with
    | [] -> ["http://helm.cs.unibo.it/dtd"; "http://mowgli.cs.unibo.it/dtd"]
    | urls -> urls
  in
  List.map (Pcre.replace ~rex) raw_urls)
let port            = lazy (
  Helm_registry.get_opt_default Helm_registry.int ~default:58081 "getter.port")

let parse_prefix_attrs s =
  List.fold_right
    (fun s acc ->
      match s with
      | "ro" -> `Read_only :: acc
      | "legacy" -> `Legacy :: acc
      | s ->
          Http_getter_logger.log ("ignoring unknown attribute: " ^ s);
          acc)
    (Pcre.split s) []

let prefixes = lazy (
  let prefixes = Helm_registry.get_list Helm_registry.string "getter.prefix" in
  List.fold_left
    (fun acc prefix ->
      let subs = Pcre.extract ~rex:prefix_RE prefix in
      try
        (subs.(1), (subs.(2), parse_prefix_attrs subs.(3))) :: acc
      with Invalid_argument _ ->
        Http_getter_logger.log ("skipping invalid prefix: " ^ prefix);
        acc)
    [] prefixes)

let host = lazy (Http_getter_misc.backtick "hostname -f")

let my_own_url =
  lazy
    (let (host, port) = (Lazy.force host, Lazy.force port) in
    sprintf "http://%s%s" (* without trailing '/' *)
    host (if port = 80 then "" else (sprintf ":%d" port)))

let env_to_string () =
  let pp_attr = function `Read_only -> "ro" | `Legacy -> "legacy" in
  let pp_prefix (uri_prefix, (url_prefix, attrs)) =
    sprintf "    %s -> %s [%s]" uri_prefix url_prefix
      (String.concat "," (List.map pp_attr attrs)) in
  let pp_prefixes prefixes =
    match prefixes with
    | [] -> ""
    | l -> "\n" ^ String.concat "\n" (List.map pp_prefix l)
  in
  sprintf
"HTTP Getter %s

prefixes:%s
dtd_dir:\t%s
host:\t\t%s
port:\t\t%d
my_own_url:\t%s
dtd_base_urls:\t%s
log_file:\t%s
log_level:\t%d
"
    version
    (pp_prefixes (Lazy.force prefixes))
    (match Lazy.force dtd_dir with Some dir -> dir | None -> "NONE")
    (Lazy.force host) (Lazy.force port)
    (Lazy.force my_own_url) (String.concat " " (Lazy.force dtd_base_urls))
    (match Http_getter_logger.get_log_file () with None -> "None" | Some f -> f)
    (Http_getter_logger.get_log_level ())

let get_dtd_dir () =
  match Lazy.force dtd_dir with
  | None -> raise (Internal_error "dtd_dir is not available")
  | Some dtd_dir -> dtd_dir

