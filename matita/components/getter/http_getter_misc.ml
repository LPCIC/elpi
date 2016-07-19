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

(* $Id: http_getter_misc.ml 7156 2007-01-10 14:30:22Z fguidi $ *)

open Printf

let file_scheme_prefix = "file://"

let trailing_dot_gz_RE = Pcre.regexp "\\.gz$"   (* for g{,un}zip *)
let url_RE = Pcre.regexp "^([\\w.-]+)(:(\\d+))?(/.*)?$"
let http_scheme_RE = Pcre.regexp ~flags:[`CASELESS] "^http://"
let file_scheme_RE = Pcre.regexp ~flags:[`CASELESS] ("^" ^ file_scheme_prefix)
let dir_sep_RE = Pcre.regexp "/"
let heading_slash_RE = Pcre.regexp "^/"

let local_url =
  let rex = Pcre.regexp ("^(" ^ file_scheme_prefix ^ ")(.*)(.gz)$") in
  fun s ->
    try
      Some ((Pcre.extract ~rex s).(2))
    with Not_found -> None

let bufsiz = 16384  (* for file system I/O *)
let tcp_bufsiz = 4096 (* for TCP I/O *)

let fold_file f init fname =
  let ic = open_in fname in
  let rec aux acc =
    let line = try Some (input_line ic) with End_of_file -> None in
    match line with
    | None -> acc
    | Some line -> aux (f line acc)
  in
  let res = try aux init with e -> close_in ic; raise e in
  close_in ic;
  res

let iter_file f = fold_file (fun line _ -> f line) ()

let iter_buf_size = 10240

let iter_file_data f fname =
  let ic = open_in fname in
  let buf = String.create iter_buf_size in
  try
    while true do
      let bytes = input ic buf 0 iter_buf_size in
      if bytes = 0 then raise End_of_file;
      f (String.sub buf 0 bytes)
    done
  with End_of_file -> close_in ic

let hashtbl_sorted_fold f tbl init =
  let sorted_keys =
    List.sort compare (Hashtbl.fold (fun key _ keys -> key::keys) tbl [])
  in
  List.fold_left (fun acc k -> f k (Hashtbl.find tbl k) acc) init sorted_keys

let hashtbl_sorted_iter f tbl =
  let sorted_keys =
    List.sort compare (Hashtbl.fold (fun key _ keys -> key::keys) tbl [])
  in
    List.iter (fun k -> f k (Hashtbl.find tbl k)) sorted_keys

let cp src dst =
  try 
    let ic = open_in src in
      try
	let oc = open_out dst in
	let buf = String.create bufsiz in
	  (try
	     while true do
	       let bytes = input ic buf 0 bufsiz in
		 if bytes = 0 then raise End_of_file else output oc buf 0 bytes
	     done
	   with 
	       End_of_file -> ()
	  );
	  close_in ic; close_out oc
      with 
	  Sys_error s -> 
	    Http_getter_logger.log s;
	    close_in ic
	| e -> 
	    Http_getter_logger.log (Printexc.to_string e);
	    close_in ic;
	    raise e
  with 
      Sys_error s -> 
	Http_getter_logger.log s
    | e -> 
	Http_getter_logger.log (Printexc.to_string e);
	raise e

let wget ?output url =
  Http_getter_logger.log
    (sprintf "wgetting %s (output: %s)" url
      (match output with None -> "default" | Some f -> f));
  match url with
  | url when Pcre.pmatch ~rex:file_scheme_RE url -> (* file:// *)
      (let src_fname = Pcre.replace ~rex:file_scheme_RE url in
      match output with
      | Some dst_fname -> cp src_fname dst_fname
      | None ->
          let dst_fname = Filename.basename src_fname in
          if src_fname <> dst_fname then
            cp src_fname dst_fname
          else  (* src and dst are the same: do nothing *)
            ())
  | url when Pcre.pmatch ~rex:http_scheme_RE url -> (* http:// *)
      (let oc = 
        open_out (match output with Some f -> f | None -> Filename.basename url)
      in
      Http_user_agent.get_iter (fun data -> output_string oc data) url;
      close_out oc)
  | scheme -> (* unsupported scheme *)
      failwith ("Http_getter_misc.wget: unsupported scheme: " ^ scheme)

let gzip ?(keep = false) ?output fname =
  let output = match output with None -> fname ^ ".gz" | Some fname -> fname in
  Http_getter_logger.log ~level:3
    (sprintf "gzipping %s (keep: %b, output: %s)" fname keep output);
  let (ic, oc) = (open_in fname, Gzip.open_out output) in
  let buf = String.create bufsiz in
  (try
    while true do
      let bytes = input ic buf 0 bufsiz in
      if bytes = 0 then raise End_of_file else Gzip.output oc buf 0 bytes
    done
  with End_of_file -> ());
  close_in ic; Gzip.close_out oc;
  if not keep then Sys.remove fname
;;

let gunzip ?(keep = false) ?output fname =
    (* assumption: given file name ends with ".gz" or output is set *)
  let output =
    match output with
    | None ->
        if (Pcre.pmatch ~rex:trailing_dot_gz_RE fname) then
          Pcre.replace ~rex:trailing_dot_gz_RE fname
        else
          failwith
            "Http_getter_misc.gunzip: unable to determine output file name"
    | Some fname -> fname
  in
  Http_getter_logger.log ~level:3
    (sprintf "gunzipping %s (keep: %b, output: %s)" fname keep output);
  (* Open the zipped file manually since Gzip.open_in may
   * leak the descriptor if it raises an exception *)
  let zic = open_in fname in
  begin
    try
      let ic = Gzip.open_in_chan zic in
      let oc = open_out output in
      let buf = String.create bufsiz in
      (try
        while true do
          let bytes = Gzip.input ic buf 0 bufsiz in
          if bytes = 0 then raise End_of_file else Pervasives.output oc buf 0 bytes
        done
      with End_of_file -> ());
	close_out oc;
	Gzip.close_in ic
    with
      e -> close_in zic ; raise e
  end ;
  if not keep then Sys.remove fname
;;

let tempfile () = Filename.temp_file "http_getter_" ""

exception Mkdir_failure of string * string;;  (* dirname, failure reason *)
let dir_perm = 0o755

let mkdir ?(parents = false) dirname =
  let mkdirhier () =
    let (pieces, hd) =
      let split = Pcre.split ~rex:dir_sep_RE dirname in
      if Pcre.pmatch ~rex:heading_slash_RE dirname then
        (List.tl split, "/")
      else
        (split, "")
    in
    ignore
      (List.fold_left
        (fun pre dir ->
          let next_dir =
            sprintf "%s%s%s" pre (match pre with "/" | "" -> "" | _ -> "/") dir
          in
          (try
            (match (Unix.stat next_dir).Unix.st_kind with
            | Unix.S_DIR -> ()  (* dir component already exists, go on! *)
            | _ ->  (* dir component already exists but isn't a dir, abort! *)
                raise
                  (Mkdir_failure (dirname,
                    sprintf "'%s' already exists but is not a dir" next_dir)))
          with Unix.Unix_error (Unix.ENOENT, "stat", _) ->
            (* dir component doesn't exists, create it and go on! *)
            Unix.mkdir next_dir dir_perm);
          next_dir)
        hd pieces)
  in
  if parents then mkdirhier () else Unix.mkdir dirname dir_perm

let string_of_proc_status = function
  | Unix.WEXITED code -> sprintf "[Exited: %d]" code
  | Unix.WSIGNALED sg -> sprintf "[Killed: %d]" sg
  | Unix.WSTOPPED sg -> sprintf "[Stopped: %d]" sg

let http_get url =
  if Pcre.pmatch ~rex:file_scheme_RE url then begin
      (* file:// URL. Read data from file system *)
    let fname = Pcre.replace ~rex:file_scheme_RE url in
    try
      let size = (Unix.stat fname).Unix.st_size in
      let buf = String.create size in
      let ic = open_in fname in
      really_input ic buf 0 size ;
      close_in ic;
      Some buf
    with Unix.Unix_error (Unix.ENOENT, "stat", _) -> None
  end else  (* other URL, pass it to Http_user_agent *)
    try
      Some (Http_user_agent.get url)
    with e ->
      Http_getter_logger.log (sprintf
        "Warning: Http_user_agent failed on url %s with exception: %s"
        url (Printexc.to_string e));
      None

let is_blank_line =
  let blank_line_RE = Pcre.regexp "(^#)|(^\\s*$)" in
  fun line ->
    Pcre.pmatch ~rex:blank_line_RE line

let normalize_dir s =  (* append "/" if missing *)
  let len = String.length s in
  try
    if s.[len - 1] = '/' then s
    else s ^ "/"
  with Invalid_argument _ -> (* string is empty *) "/"

let strip_trailing_slash s =
  try
    let len = String.length s in
    if s.[len - 1] = '/' then String.sub s 0 (len - 1)
    else s
  with Invalid_argument _ -> s

let strip_suffix ~suffix s =
  try
    let s_len = String.length s in
    let suffix_len = String.length suffix in
    let suffix_sub = String.sub s (s_len - suffix_len) suffix_len in
    if suffix_sub <> suffix then raise (Invalid_argument "Http_getter_misc.strip_suffix");
    String.sub s 0 (s_len - suffix_len)
  with Invalid_argument _ ->
    raise (Invalid_argument "Http_getter_misc.strip_suffix")

let rec list_uniq = function 
  | [] -> []
  | h::[] -> [h]
  | h1::h2::tl when h1 = h2 -> list_uniq (h2 :: tl) 
  | h1::tl (* when h1 <> h2 *) -> h1 :: list_uniq tl

let extension s =
  try
    let idx = String.rindex s '.' in
    String.sub s idx (String.length s - idx)
  with Not_found -> ""

let temp_file_of_uri uri =
  let flat_string s s' c =
    let cs = String.copy s in
    for i = 0 to (String.length s) - 1 do
      if String.contains s' s.[i] then cs.[i] <- c
    done;
    cs
  in
  let user = try Unix.getlogin () with _ -> "" in
  Filename.open_temp_file (user ^ flat_string uri ".-=:;!?/&" '_') ""

let backtick cmd =
  let ic = Unix.open_process_in cmd in
  let res = input_line ic in
  ignore (Unix.close_process_in ic);
  res

