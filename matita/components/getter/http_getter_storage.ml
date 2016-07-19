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

(* $Id: http_getter_storage.ml 7472 2007-07-06 14:49:47Z tassi $ *)

open Printf

open Http_getter_misc
open Http_getter_types

exception Not_found'
exception Resource_not_found of string * string  (** method, uri *)

let index_fname = "INDEX"

(******************************* HELPERS **************************************)

let trailing_slash_RE = Pcre.regexp "/$"
let relative_RE_raw = "(^[^/]+(/[^/]+)*/?$)"
let relative_RE = Pcre.regexp relative_RE_raw
let file_scheme_RE_raw = "(^file://)"
let extended_file_scheme_RE = Pcre.regexp "(^file:/+)"
let file_scheme_RE = Pcre.regexp (relative_RE_raw ^ "|" ^ file_scheme_RE_raw)
let http_scheme_RE = Pcre.regexp "^http://"
let newline_RE = Pcre.regexp "\\n"
let cic_scheme_sep_RE = Pcre.regexp ":/"
let gz_suffix = ".gz"
let gz_suffix_len = String.length gz_suffix

  (* file:///bla -> bla, bla -> bla *)
let path_of_file_url url =
  assert (Pcre.pmatch ~rex:file_scheme_RE url);
  if Pcre.pmatch ~rex:relative_RE url then
    url
  else  (* absolute path, add heading "/" if missing *)
    "/" ^ (Pcre.replace ~rex:extended_file_scheme_RE url)

let strip_gz_suffix fname =
  if extension fname = gz_suffix then
    String.sub fname 0 (String.length fname - gz_suffix_len)
  else
    fname

let normalize_root uri =  (* add trailing slash to roots *)
  try
    if uri.[String.length uri - 1] = ':' then uri ^ "/"
    else uri
  with Invalid_argument _ -> uri

let remove_duplicates l =
  Http_getter_misc.list_uniq (List.stable_sort Pervasives.compare l)

let has_rdonly l =  List.exists ((=) `Read_only) l
let has_legacy l =  List.exists ((=) `Legacy) l
let is_readwrite attrs = (not (has_legacy attrs) && not (has_rdonly attrs))

let is_file_schema url = Pcre.pmatch ~rex:file_scheme_RE url
let is_http_schema url = Pcre.pmatch ~rex:http_scheme_RE url

let is_empty_listing files = 
  List.for_all
   (fun s ->
     let len = String.length s in
      len < 4 || String.sub s (len - 4) 4 <> ".xml") files

(************************* GLOBALS PREFIXES **********************************)
    
  (** associative list regular expressions -> url prefixes
   * sorted with longest prefixes first *)
let prefix_map_ref = ref (lazy (
  List.map
    (fun (uri_prefix, (url_prefix, attrs)) ->
      let uri_prefix = normalize_dir uri_prefix in
      let url_prefix = normalize_dir url_prefix in
      let regexp = Pcre.regexp ("^(" ^ Pcre.quote uri_prefix ^ ")") in
      regexp, strip_trailing_slash uri_prefix, url_prefix, attrs)
    (List.rev (Lazy.force Http_getter_env.prefixes))))

let prefix_map () = !prefix_map_ref

let keep_first l = 
  let cmp (_,x) (_,y) = x = y in
  let rec aux prev = function
    | [] -> []
    | hd::tl -> if cmp prev hd then hd :: aux prev tl else []
  in
  match l with
  | hd :: tl -> hd :: aux hd tl
  | _ -> assert false
;;

  (** given an uri returns the prefixes for it *)
let lookup uri =
  let matches =
    HExtlib.filter_map 
      (fun (rex, _, l, _ as entry) -> 
         try
           let got = Pcre.extract ~full_match:true ~rex uri in
           Some (entry, String.length got.(0))
         with Not_found -> None)
      (Lazy.force (prefix_map ())) 
  in
  if matches = [] then raise (Unresolvable_URI uri);
  List.map fst (keep_first (List.sort (fun (_,l1) (_,l2) -> l2 - l1) matches))
;;

let get_attrs uri = List.map (fun (_, _, _, attrs) -> attrs) (lookup uri)

(*************************** ACTIONS ******************************************)
  
let exists_http ~local _ url =
  if local then false else
  Http_getter_wget.exists (url ^ gz_suffix) || Http_getter_wget.exists url

let exists_file _ fname =
  Sys.file_exists (fname ^ gz_suffix) || Sys.file_exists fname

let resolve_http ~must_exists ~local _ url =
  if local then raise Not_found' else
  try
    if must_exists then
      List.find Http_getter_wget.exists [ url ^ gz_suffix; url ]
    else
      url
  with Not_found -> raise Not_found'

let resolve_file ~must_exists _ fname =
  try
    if must_exists then
      List.find Sys.file_exists [ fname ^ gz_suffix; fname ]
    else
      fname
  with Not_found -> raise Not_found'

let ls_file_single _ path_prefix =
  let is_dir fname = (Unix.stat fname).Unix.st_kind = Unix.S_DIR in
  let is_useless dir = try dir.[0] = '.' with _ -> false in
  let entries = ref [] in
  try
    let dir_handle = Unix.opendir path_prefix in
    (try
      while true do
        let entry = Unix.readdir dir_handle in
        if is_useless entry then
          ()
        else if is_dir (path_prefix ^ "/" ^ entry) then
          entries := normalize_dir entry :: !entries
        else
          entries := strip_gz_suffix entry :: !entries
      done
    with End_of_file -> Unix.closedir dir_handle);
    remove_duplicates !entries
  with Unix.Unix_error (_, "opendir", _) -> []

let ls_http_single ~local _ url_prefix =
  if local then raise (Resource_not_found ("get","")) else
  let url = normalize_dir url_prefix ^ index_fname in
  try
    let index = Http_getter_wget.get url in
    Pcre.split ~rex:newline_RE index
  with Http_client_error _ -> raise (Resource_not_found ("get",url))
;;

let get_file _ path =
  if Sys.file_exists (path ^ gz_suffix) then
    path ^ gz_suffix
  else if Sys.file_exists path then
    path
  else
    raise Not_found'

let get_http ~local uri url =
  if local then raise Not_found' else
  let scheme, path =
    match Pcre.split ~rex:cic_scheme_sep_RE uri with
    | [scheme; path] -> scheme, path
    | _ -> assert false
  in
  let cache_name =
    sprintf "%s%s/%s" (Lazy.force Http_getter_env.cache_dir) scheme path
  in
  if Sys.file_exists (cache_name ^ gz_suffix) then
    cache_name ^ gz_suffix
  else if Sys.file_exists cache_name then
    cache_name
  else begin  (* fill cache *)
    Http_getter_misc.mkdir ~parents:true (Filename.dirname cache_name);
    (try
      Http_getter_wget.get_and_save (url ^ gz_suffix) (cache_name ^ gz_suffix);
      cache_name ^ gz_suffix
    with Http_client_error _ ->
      (try
        Http_getter_wget.get_and_save url cache_name;
        cache_name
      with Http_client_error _ ->
        raise Not_found'))
  end

let remove_file _ path =
  if Sys.file_exists (path ^ gz_suffix) then Sys.remove (path ^ gz_suffix);
  if Sys.file_exists path then Sys.remove path

let remove_http _ _ =
  prerr_endline "Http_getter_storage.remove: not implemented for HTTP scheme";
  assert false

(**************************** RESOLUTION OF PREFIXES ************************)
  
let resolve_prefixes n local write exists uri =
  let exists_test new_uri =
    if is_file_schema new_uri then 
      exists_file () (path_of_file_url new_uri)
    else if is_http_schema new_uri then
      exists_http ~local () new_uri
    else false
  in
  let rec aux n = function
    | (rex, _, url_prefix, attrs) :: tl when n > 0->
        (match write, is_readwrite attrs, exists with
        | true ,false, _ -> aux n tl
        | true ,true ,true  
        | false,_ ,true ->
            let new_uri = (Pcre.replace_first ~rex ~templ:url_prefix uri) in
            if exists_test new_uri then new_uri::aux (n-1) tl else aux n tl
        | true ,true ,false
        | false,_ ,false -> 
            (Pcre.replace_first ~rex ~templ:url_prefix uri) :: (aux (n-1) tl))
    | _ -> []
  in
  aux n (lookup uri)

let resolve_prefix l w e u =
  match resolve_prefixes 1 l w e u with
  | hd :: _ -> hd
  | [] -> 
      raise 
        (Resource_not_found 
          (Printf.sprintf "resolve_prefix write:%b exists:%b" w e,u))
  
(* uncomment to debug prefix resolution *)
(*
let resolve_prefix w e u =
  prerr_endline 
    ("XXX w=" ^ string_of_bool w ^ " e=" ^ string_of_bool e ^" :" ^ u);
  let rc = resolve_prefix w e u in
  prerr_endline ("YYY :" ^ rc ^ "\n");
  rc 
*)

(************************* DISPATCHERS ***************************************)

type 'a storage_method = {
  name: string;
  write: bool;
  exists: bool;
  local: bool;
  file: string -> string -> 'a; (* unresolved uri, resolved uri *)
  http: string -> string -> 'a; (* unresolved uri, resolved uri *)
}

let invoke_method storage_method uri url =
  try
    if is_file_schema url then 
      storage_method.file uri (path_of_file_url url)
    else if is_http_schema url then
      storage_method.http uri url
    else
      raise (Unsupported_scheme url)
  with Not_found' -> raise (Resource_not_found (storage_method.name, uri))
  
let dispatch_single storage_method uri =
  assert (extension uri <> gz_suffix);
  let uri = normalize_root uri in
  let url = 
    resolve_prefix 
      storage_method.local storage_method.write storage_method.exists uri 
  in
  invoke_method storage_method uri url

let dispatch_multi storage_method uri =
  let urls = 
    resolve_prefixes max_int
      storage_method.local storage_method.write storage_method.exists uri 
  in
  let rec aux = function
    | [] -> raise (Resource_not_found (storage_method.name, uri))
    | url :: tl ->
        (try
          invoke_method storage_method uri url
        with Resource_not_found _ -> aux tl)
  in
  aux urls

let dispatch_all storage_method uri =
  let urls = 
    resolve_prefixes max_int
      storage_method.local storage_method.write storage_method.exists uri 
  in
  List.map (fun url -> invoke_method storage_method uri url) urls
 
(******************************** EXPORTED FUNCTIONS *************************)
  
let exists ~local s =
  try 
    dispatch_single 
    { write = false; 
      name = "exists"; 
      exists = true;
      local=local;
      file = exists_file; http = exists_http ~local; } s
  with Resource_not_found _ -> false

let resolve ~local ?(must_exists=true) ~writable =
  (if must_exists then
    dispatch_multi
  else
    dispatch_single)
    { write = writable;
      name="resolve"; 
      exists = must_exists;
      local=local;
      file = resolve_file ~must_exists; 
      http = resolve_http ~local ~must_exists; }

let remove =
  dispatch_single 
    { write = false;
      name = "remove"; 
      exists=true;
      local=false;
      file = remove_file; http = remove_http; }

let filename ~local ?(find = false) =
  (if find then dispatch_multi else dispatch_single)
    { write = false;
      name = "filename"; 
      exists=true;
      local=local;
      file = get_file; http = get_http ~local ; }

let ls ~local uri_prefix =
  let ls_all s =
    try 
      dispatch_all 
        { write=false;
          name = "ls"; 
          exists=true;
          local=local;
          file = ls_file_single; http = ls_http_single ~local; } s
    with Resource_not_found _ -> []
  in 
  let direct_results = List.flatten (ls_all uri_prefix) in
  List.fold_left
    (fun results (_, uri_prefix', _, _) ->
      if Filename.dirname uri_prefix' = strip_trailing_slash uri_prefix then
        (Filename.basename uri_prefix' ^ "/") :: results
      else
        results)
    direct_results
    (Lazy.force (prefix_map ()))

let clean_cache () =
  ignore (Sys.command
    (sprintf "rm -rf %s/" (Lazy.force Http_getter_env.cache_dir)))
 
let list_writable_prefixes _ =
  HExtlib.filter_map 
    (fun (_,_,url,attrs) -> 
      if is_readwrite attrs then 
        Some url 
      else 
        None) 
    (Lazy.force (prefix_map ()))

let is_legacy uri = List.for_all has_legacy (get_attrs uri) 

(* implement this in a fast way! *)
let is_empty ~local buri =
  let buri = strip_trailing_slash buri ^ "/" in
  let files = ls ~local buri in
  is_empty_listing files

let is_read_only uri = 
  let is_empty_dir path =
    let files = 
      try
        if is_file_schema path then 
          ls_file_single () (path_of_file_url path)
        else if is_http_schema path then
          ls_http_single ~local:false () path
        else 
          assert false
      with Resource_not_found _ -> []
    in
    is_empty_listing files
  in
  let rec aux found_writable = function
    | (rex, _, url_prefix, attrs)::tl -> 
        let new_url = (Pcre.replace_first ~rex ~templ:url_prefix uri) in
        let rdonly = has_legacy attrs || has_rdonly attrs in
        (match rdonly, is_empty_dir new_url, found_writable with
        | true, false, _ -> true
        | true, true, _ -> aux found_writable tl
        | false, _, _ -> aux true tl)
    | [] -> not found_writable (* if found_writable then false else true *)
  in 
  aux false (lookup uri)

let activate_system_mode () =
  let map = Lazy.force (prefix_map ()) in
  let map = 
    HExtlib.filter_map 
      (fun ((rex, urip, urlp, attrs) as entry) -> 
         if has_legacy attrs then
           Some entry
         else if has_rdonly attrs then
           Some (rex, urip, urlp, List.filter ((<>) `Read_only) attrs)
         else
           None) 
      map
  in
  let map = map in (* just to remember that ocamlc 'lazy' is a ... *)
  prefix_map_ref := (lazy map)

(* eof *)
