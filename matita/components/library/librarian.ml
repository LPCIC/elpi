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

exception FileNotFound of string
exception NoRootFor of string

let absolutize path =
 let path = 
   if String.length path > 0 && path.[0] <> '/' then
     Sys.getcwd () ^ "/" ^ path
   else 
     path
 in
   HExtlib.normalize_path path
;;


let find_root path =
  let path = absolutize path in
  let paths = List.rev (Str.split (Str.regexp "/") path) in
  let rec build = function
    | he::tl as l -> ("/" ^ String.concat "/" (List.rev l) ^ "/") :: build tl
    | [] -> ["/"]
  in
  let paths = List.map HExtlib.normalize_path (build paths) in
  try HExtlib.find_in paths "root"
  with Failure "find_in" -> 
    raise (NoRootFor (path ^ " (" ^ String.concat ", " paths ^ ")"))
;;
  
let ensure_trailing_slash s = 
  if s = "" then "/" else
  if s.[String.length s-1] <> '/' then s^"/" else s
;;

let remove_trailing_slash s = 
  if s = "" then "" else
  let len = String.length s in
  if s.[len-1] = '/' then String.sub s 0 (len-1) else s
;;

let load_root_file rootpath =
  let data = HExtlib.input_file rootpath in
  let lines = Str.split (Str.regexp "\n") data in
  let clean s = 
    Pcre.replace ~pat:"[ \t]+" ~templ:" "
      (Pcre.replace ~pat:"^ *" (Pcre.replace ~pat:" *$" s))
  in
  List.map 
    (fun l -> 
      match Str.split (Str.regexp "=") l with
      | [k;v] -> clean k, Http_getter_misc.strip_trailing_slash (clean v)
      | _ -> raise (Failure ("Malformed root file: " ^ rootpath)))
    lines
;;

let find_root_for ~include_paths file = 
  let include_paths = "" :: Sys.getcwd () :: include_paths in
   let rec find_path_for file =
      try HExtlib.find_in include_paths file
      with Failure "find_in" -> 
       HLog.error ("We are in: " ^ Sys.getcwd ());
       HLog.error ("Unable to find: "^file^"\nPaths explored:");
       List.iter (fun x -> HLog.error (" - "^x)) include_paths;
       raise (FileNotFound file)
   in
   let path = find_path_for file in   
   let path = absolutize path in
(*     HLog.debug ("file "^file^" resolved as "^path);  *)
   let rootpath, root, buri = 
     try
       let mburi = Helm_registry.get "matita.baseuri" in
       match Str.split (Str.regexp " ") mburi with
       | [root; buri] when HExtlib.is_prefix_of root path -> 
           ":registry:", root, buri
       | _ -> raise (Helm_registry.Key_not_found "matita.baseuri")
     with Helm_registry.Key_not_found "matita.baseuri" -> 
       let rootpath = find_root path in
       let buri = List.assoc "baseuri" (load_root_file rootpath) in
       rootpath, Filename.dirname rootpath, buri
   in
(*     HLog.debug ("file "^file^" rooted by "^rootpath^"");  *)
   let uri = Http_getter_misc.strip_trailing_slash buri in
   if String.length uri < 5 || String.sub uri 0 5 <> "cic:/" then
     HLog.error (rootpath ^ " sets an incorrect baseuri: " ^ buri);
   ensure_trailing_slash root, remove_trailing_slash uri, path
 
;;

let mk_baseuri root extra =
  let chop name = 
(* FG: there is no reason why matita should edit just matita files
       matita's editor is good on its own and has interesting facilities
       including predefined virtuals
    assert(Filename.check_suffix name ".ma" ||
      Filename.check_suffix name ".mma");
*)    
    try Filename.chop_extension name
    with Invalid_argument "Filename.chop_extension" -> name
  in
   remove_trailing_slash (HExtlib.normalize_path (root ^ "/" ^ chop extra))
;;

let baseuri_of_script ~include_paths file = 
  let root, buri, path = find_root_for ~include_paths file in
  let path = HExtlib.normalize_path path in
  let root = HExtlib.normalize_path root in
  let lpath = Str.split (Str.regexp "/") path in
  let lroot = Str.split (Str.regexp "/") root in
  let rec substract l1 l2 =
    match l1, l2 with
    | h1::tl1,h2::tl2 when h1 = h2 -> substract tl1 tl2
    | l,[] -> l
    | _ -> assert false
  in
  let extra_buri = substract lpath lroot in
  let extra = String.concat "/" extra_buri in
   root,
   mk_baseuri buri extra,
   path,
   extra
;;

let find_roots_in_dir dir =
  HExtlib.find ~test:(fun f ->
    Filename.basename f = "root" &&
    try (Unix.stat f).Unix.st_kind = Unix.S_REG 
    with Unix.Unix_error _ -> false)
    dir
;;

(* scheme uri part as defined in URI Generic Syntax (RFC 3986) *)
let uri_scheme_rex = Pcre.regexp "^[[:alpha:]][[:alnum:]\-+.]*:"

let is_uri str = Pcre.pmatch ~rex:uri_scheme_rex str
