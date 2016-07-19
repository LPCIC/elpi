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

(* $Id: http_getter.ml 11008 2010-10-26 14:32:14Z asperti $ *)

open Printf

open Http_getter_common
open Http_getter_misc
open Http_getter_types

exception Not_implemented of string
exception UnexpectedGetterOutput

type resolve_result =
  | Unknown
  | Exception of exn
  | Resolved of string

type logger_callback = HelmLogger.html_tag -> unit

let stdout_logger tag = print_string (HelmLogger.string_of_html_tag tag)

let not_implemented s = raise (Not_implemented ("Http_getter." ^ s))

let index_line_sep_RE     = Pcre.regexp "[ \t]+"
let index_sep_RE          = Pcre.regexp "\r\n|\r|\n"
let trailing_types_RE     = Pcre.regexp "\\.types$"
let heading_cic_RE        = Pcre.regexp "^cic:"
let heading_theory_RE     = Pcre.regexp "^theory:"
let heading_nuprl_RE      = Pcre.regexp "^nuprl:"
let types_RE              = Pcre.regexp "\\.types$"
let types_ann_RE          = Pcre.regexp "\\.types\\.ann$"
let body_RE               = Pcre.regexp "\\.body$"
let body_ann_RE           = Pcre.regexp "\\.body\\.ann$"
let proof_tree_RE         = Pcre.regexp "\\.proof_tree$"
let proof_tree_ann_RE     = Pcre.regexp "\\.proof_tree\\.ann$"
let theory_RE             = Pcre.regexp "\\.theory$"
let basepart_RE           = Pcre.regexp
  "^([^.]*\\.[^.]*)((\\.body)|(\\.proof_tree)|(\\.types))?(\\.ann)?$"
let slash_RE              = Pcre.regexp "/"
let pipe_RE               = Pcre.regexp "\\|"
let til_slash_RE          = Pcre.regexp "^.*/"
let no_slashes_RE         = Pcre.regexp "^[^/]*$"
let fix_regexp_RE         = Pcre.regexp ("^" ^ (Pcre.quote "(cic|theory)"))
let showable_file_RE      =
  Pcre.regexp "(\\.con|\\.ind|\\.var|\\.body|\\.types|\\.proof_tree)$"

let xml_suffix = ".xml"
let theory_suffix = ".theory"

  (* global maps, shared by all threads *)

let ends_with_slash s =
  try
    s.[String.length s - 1] = '/'
  with Invalid_argument _ -> false

  (* should we use a remote getter or not *)
let remote () =
  try
    Helm_registry.get "getter.mode" = "remote"
  with Helm_registry.Key_not_found _ -> false

let getter_url () = Helm_registry.get "getter.url"

(* Remote interface: getter methods implemented using a remote getter *)

  (* <TODO> *)
let getxml_remote uri = not_implemented "getxml_remote"
let getxslt_remote uri = not_implemented "getxslt_remote"
let getdtd_remote uri = not_implemented "getdtd_remote"
let clean_cache_remote () = not_implemented "clean_cache_remote"
let list_servers_remote () = not_implemented "list_servers_remote"
let add_server_remote ~logger ~position name =
  not_implemented "add_server_remote"
let remove_server_remote ~logger position =
  not_implemented "remove_server_remote"
let getalluris_remote () = not_implemented "getalluris_remote"
let ls_remote lsuri = not_implemented "ls_remote"
let exists_remote uri = not_implemented "exists_remote"
  (* </TODO> *)

let resolve_remote ~writable uri =
  (* deliver resolve request to http_getter *)
  let doc =
    Http_getter_wget.get (sprintf "%sresolve?uri=%s&writable=%b" (getter_url ())
      uri writable)
  in
  let res = ref Unknown in
  let start_element tag attrs =
    match tag with
    | "url" ->
        (try
          res := Resolved (List.assoc "value" attrs)
        with Not_found -> ())
    | "unresolvable" -> res := Exception (Unresolvable_URI uri)
    | "not_found" -> res := Exception (Key_not_found uri)
    | _ -> ()
  in
  let callbacks = {
    XmlPushParser.default_callbacks with
      XmlPushParser.start_element = Some start_element
  } in
  let xml_parser = XmlPushParser.create_parser callbacks in
  XmlPushParser.parse xml_parser (`String doc);
  XmlPushParser.final xml_parser;
  match !res with
  | Unknown -> raise UnexpectedGetterOutput
  | Exception e -> raise e
  | Resolved url -> url

let deref_index_theory ~local uri =
(*  if Http_getter_storage.exists ~local (uri ^ xml_suffix) then uri *)
 if is_theory_uri uri && Filename.basename uri = "index.theory" then
    strip_trailing_slash (Filename.dirname uri) ^ theory_suffix
 else
    uri

(* API *)

let help () = Http_getter_const.usage_string (Http_getter_env.env_to_string ())

let exists ~local uri =
(*   prerr_endline ("Http_getter.exists " ^ uri); *)
  if remote () then
    exists_remote uri
  else
   let uri = deref_index_theory ~local uri in
    Http_getter_storage.exists ~local (uri ^ xml_suffix)
	
let is_an_obj s = s <> NUri.baseuri_of_uri (NUri.uri_of_string s)
    
let resolve ~local ~writable uri =
  if remote () then
    resolve_remote ~writable uri
  else
   let uri = deref_index_theory ~local uri in
    try
      if is_an_obj uri then
        Http_getter_storage.resolve ~writable ~local (uri ^ xml_suffix)
      else
        Http_getter_storage.resolve ~writable ~local uri
    with Http_getter_storage.Resource_not_found _ -> raise (Key_not_found uri)

let filename ~local ~writable uri =
  if remote () then
    raise (Key_not_found uri)
  else
   let uri = deref_index_theory ~local uri in
    try
      Http_getter_storage.resolve 
        ~must_exists:false ~writable ~local uri
    with Http_getter_storage.Resource_not_found _ -> raise (Key_not_found uri)

let getxml uri =
  if remote () then getxml_remote uri
  else begin
    let uri' = deref_index_theory ~local:false uri in
    (try
      Http_getter_storage.filename ~local:false (uri' ^ xml_suffix)
    with Http_getter_storage.Resource_not_found _ -> raise (Key_not_found uri))
  end

let getxslt uri =
  if remote () then getxslt_remote uri
  else Http_getter_storage.filename ~local:false ~find:true ("xslt:/" ^ uri)

let getdtd uri =
  if remote () then
    getdtd_remote uri
  else begin
    let fname = Http_getter_env.get_dtd_dir () ^ "/" ^ uri in
    if not (Sys.file_exists fname) then raise (Dtd_not_found uri);
    fname
  end

let clean_cache () =
  if remote () then
    clean_cache_remote ()
  else
    Http_getter_storage.clean_cache ()

let (++) (oldann, oldtypes, oldbody, oldtree)
         (newann, newtypes, newbody, newtree) =
  ((if newann   > oldann    then newann   else oldann),
   (if newtypes > oldtypes  then newtypes else oldtypes),
   (if newbody  > oldbody   then newbody  else oldbody),
   (if newtree  > oldtree   then newtree  else oldtree))
    
let store_obj tbl o =
(*   prerr_endline ("Http_getter.store_obj " ^ o); *)
  if Pcre.pmatch ~rex:showable_file_RE o then begin
    let basepart = Pcre.replace ~rex:basepart_RE ~templ:"$1" o in
    let no_flags = false, No, No, No in
    let oldflags =
      try
        Hashtbl.find tbl basepart
      with Not_found -> (* no ann, no types, no body, no proof tree *)
        no_flags
    in
    let newflags =
      match o with
      | s when Pcre.pmatch ~rex:types_RE s          -> (false, Yes, No, No)
      | s when Pcre.pmatch ~rex:types_ann_RE s      -> (true,  Ann, No, No)
      | s when Pcre.pmatch ~rex:body_RE s           -> (false, No, Yes, No)
      | s when Pcre.pmatch ~rex:body_ann_RE s       -> (true,  No, Ann, No)
      | s when Pcre.pmatch ~rex:proof_tree_RE s     -> (false, No, No, Yes)
      | s when Pcre.pmatch ~rex:proof_tree_ann_RE s -> (true,  No, No, Ann)
      | s -> no_flags
    in
    Hashtbl.replace tbl basepart (oldflags ++ newflags)
  end
  
let store_dir set_ref d =
  set_ref := StringSet.add (List.hd (Pcre.split ~rex:slash_RE d)) !set_ref

let collect_ls_items dirs_set objs_tbl =
  let items = ref [] in
  StringSet.iter (fun dir -> items := Ls_section dir :: !items) dirs_set;
  Http_getter_misc.hashtbl_sorted_iter
    (fun uri (annflag, typesflag, bodyflag, treeflag) ->
      items :=
        Ls_object {
          uri = uri; ann = annflag;
          types = typesflag; body = bodyflag; proof_tree = treeflag
        } :: !items)
    objs_tbl;
  List.rev !items

let contains_object = (<>) []

  (** non regexp-aware version of ls *)
let rec dumb_ls ~local uri_prefix =
(*   prerr_endline ("Http_getter.dumb_ls " ^ uri_prefix); *)
  if is_cic_obj_uri uri_prefix then begin
    let dirs = ref StringSet.empty in
    let objs = Hashtbl.create 17 in
    List.iter
      (fun fname ->
        if ends_with_slash fname then
          store_dir dirs fname
        else
          try
            store_obj objs (strip_suffix ~suffix:xml_suffix fname)
          with Invalid_argument _ -> ())
      (Http_getter_storage.ls ~local uri_prefix);
    collect_ls_items !dirs objs
  end else if is_theory_uri uri_prefix then begin
    let items = ref [] in
    let add_theory fname =
      items :=
        Ls_object {
          uri = fname; ann = false; types = No; body = No; proof_tree = No }
        :: !items
    in
    let cic_uri_prefix =
      Pcre.replace_first ~rex:heading_theory_RE ~templ:"cic:" uri_prefix
    in
    List.iter
      (fun fname ->
        if ends_with_slash fname then
          items := Ls_section (strip_trailing_slash fname) :: !items
        else
          try
            let fname = strip_suffix ~suffix:xml_suffix fname in
            let theory_name = strip_suffix ~suffix:theory_suffix fname in
            let sub_theory = normalize_dir cic_uri_prefix ^ theory_name ^ "/" in
            if is_empty_theory ~local sub_theory then add_theory fname
          with Invalid_argument _ -> ())
      (Http_getter_storage.ls ~local uri_prefix);
    (try
      if contains_object (dumb_ls ~local cic_uri_prefix)
        && exists ~local:false (strip_trailing_slash uri_prefix ^ theory_suffix)
      then
        add_theory "index.theory";
    with Unresolvable_URI _ -> ());
    !items
  end else
    raise (Invalid_URI uri_prefix)

and is_empty_theory ~local uri_prefix =
(*   prerr_endline ("is_empty_theory " ^ uri_prefix); *)
  not (contains_object (dumb_ls ~local uri_prefix))

  (* handle simple regular expressions of the form "...(..|..|..)..." on cic
   * uris, not meant to be a real implementation of regexp. The only we use is
   * "(cic|theory):/..." *)
let explode_ls_regexp regexp =
  try
    let len = String.length regexp in
    let lparen_idx = String.index regexp '(' in
    let rparen_idx = String.index_from regexp lparen_idx ')' in
    let choices_str = (* substring between parens, parens excluded *)
      String.sub regexp (lparen_idx + 1) (rparen_idx - lparen_idx - 1)
    in
    let choices = Pcre.split ~rex:pipe_RE choices_str in
    let prefix = String.sub regexp 0 lparen_idx in
    let suffix = String.sub regexp (rparen_idx + 1) (len - (rparen_idx + 1)) in
    List.map (fun choice -> prefix ^ choice ^ suffix) choices
  with Not_found -> [regexp]

let merge_results results =
  let rec aux objects_acc dirs_acc = function
    | [] -> dirs_acc @ objects_acc
    | Ls_object _ as obj :: tl -> aux (obj :: objects_acc) dirs_acc tl
    | Ls_section _ as dir :: tl ->
        if List.mem dir dirs_acc then (* filters out dir duplicates *)
          aux objects_acc dirs_acc tl
        else
          aux objects_acc (dir :: dirs_acc) tl
  in
  aux [] [] (List.concat results)

let ls ~local regexp =
  if remote () then
    ls_remote regexp
  else
    let prefixes = explode_ls_regexp regexp in
    merge_results (List.map (dumb_ls ~local) prefixes)

let getalluris () =
  let rec aux acc = function
    | [] -> acc
    | dir :: todo ->
        let acc', todo' =
          List.fold_left
            (fun (acc, subdirs) result ->
              match result with
              | Ls_object obj -> (dir ^ obj.uri) :: acc, subdirs
              | Ls_section sect -> acc, (dir ^ sect ^ "/") :: subdirs)
            (acc, todo)
            (dumb_ls ~local:false dir)
        in
        aux acc' todo'
  in
  aux [] ["cic:/"] (* trailing slash required *)

(* Shorthands from now on *)

let getxml' uri = getxml (NUri.string_of_uri uri)
let resolve' ~local ~writable uri =
  resolve ~local ~writable (NUri.string_of_uri uri)
;;
let exists' ~local uri = exists ~local (NUri.string_of_uri uri)
let filename' ~local ~writable uri =
  filename ~local ~writable (NUri.string_of_uri uri)
;;

let tilde_expand_key k =
  try
    Helm_registry.set k (HExtlib.tilde_expand (Helm_registry.get k))
  with Helm_registry.Key_not_found _ -> ()

let init () =
  List.iter tilde_expand_key ["getter.cache_dir"; "getter.dtd_dir"];
  Http_getter_logger.set_log_level
    (Helm_registry.get_opt_default Helm_registry.int ~default:1
      "getter.log_level");
  Http_getter_logger.set_log_file
    (Helm_registry.get_opt Helm_registry.string "getter.log_file")

