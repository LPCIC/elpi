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

(* $Id: libraryClean.ml 11124 2010-12-16 17:10:54Z sacerdot $ *)

open Printf

let debug = false
let debug_prerr = if debug then prerr_endline else ignore

module HGT = Http_getter_types;;
module HG = Http_getter;;
(*module UM = UriManager;;*)

let decompile = ref (fun ~baseuri -> assert false);;
let set_decompile_cb f = decompile := f;;

(*
let strip_xpointer s = Pcre.replace ~pat:"#.*$" s ;;

let safe_buri_of_suri suri =
  try
    UM.buri_of_uri (UM.uri_of_string suri)
  with
    UM.IllFormedUri _ -> suri

let one_step_depend cache_of_processed_baseuri suri dbtype dbd =
  assert false (* MATITA 1.0
  let buri = safe_buri_of_suri suri in
  if Hashtbl.mem cache_of_processed_baseuri buri then 
    []
  else
    begin
      Hashtbl.add cache_of_processed_baseuri buri true;
      let query = 
        let buri = buri ^ "/" in 
        let buri = HSql.escape dbtype dbd buri in
        let obj_tbl = MetadataTypes.obj_tbl () in
        if HSql.isMysql dbtype dbd then        
          sprintf ("SELECT source, h_occurrence FROM %s WHERE " 
            ^^ "h_occurrence REGEXP '"^^
            "^%s\\([^/]+\\|[^/]+#xpointer.*\\)$"^^"'")
          obj_tbl buri
      	else
	  begin
            sprintf ("SELECT source, h_occurrence FROM %s WHERE " 
            ^^ "REGEXP(h_occurrence, '"^^
            "^%s\\([^/]+\\|[^/]+#xpointer.*\\)$"^^"')")
            obj_tbl buri
            (* implementation with vanilla ocaml-sqlite3
            HLog.debug "Warning SELECT without REGEXP";
      	    sprintf
              ("SELECT source, h_occurrence FROM %s WHERE " ^^ 
               "h_occurrence LIKE '%s%%' " ^^ HSql.escape_string_for_like)
           	  obj_tbl buri*)
	  end
      in
      try 
        let rc = HSql.exec dbtype dbd query in
        let l = ref [] in
        HSql.iter rc (
          fun row -> 
            match row.(0), row.(1) with 
            | Some uri, Some occ when 
                Filename.dirname (strip_xpointer occ) = buri -> 
                  l := uri :: !l
            | _ -> ());
        let l = List.sort Pervasives.compare !l in
        HExtlib.list_uniq l
      with
        exn -> raise exn (* no errors should be accepted *)
    end
    *)
    
let db_uris_of_baseuri buri =
  [] (* MATITA 1.0
 let dbd = LibraryDb.instance () in
 let dbtype = 
   if Helm_registry.get_bool "matita.system" then HSql.Library else HSql.User
 in
 let query = 
  let buri = buri ^ "/" in 
  let buri = HSql.escape dbtype dbd buri in
  let obj_tbl = MetadataTypes.name_tbl () in
  if HSql.isMysql dbtype dbd then        
    sprintf ("SELECT source FROM %s WHERE " 
    ^^ "source REGEXP '^%s[^/]*(#xpointer.*)?$'") obj_tbl buri
  else
   begin
    sprintf ("SELECT source FROM %s WHERE " 
      ^^ "REGEXP(source, '^%s[^/]*\\(#xpointer.*\\)?$')") obj_tbl buri
   end
 in
 try 
  let rc = HSql.exec dbtype dbd query in
  let l = ref [] in
  HSql.iter rc (
    fun row -> 
      match row.(0) with 
      | Some uri when Filename.dirname (strip_xpointer uri) = buri -> 
          l := uri :: !l
      | _ -> ());
  let l = List.sort Pervasives.compare !l in
  HExtlib.list_uniq l
 with
  exn -> raise exn (* no errors should be accepted *)
  *)
;;

let close_uri_list cache_of_processed_baseuri uri_to_remove =
  let dbd = LibraryDb.instance () in
  let dbtype = 
    if Helm_registry.get_bool "matita.system" then HSql.Library else HSql.User
  in
  (* to remove an uri you have to remove the whole script *)
  let buri_to_remove = 
    HExtlib.list_uniq 
      (List.fast_sort Pervasives.compare 
        (List.map safe_buri_of_suri uri_to_remove))
  in
  (* cleand the already visided baseuris *)
  let buri_to_remove = 
    List.filter 
      (fun buri -> 
        if Hashtbl.mem cache_of_processed_baseuri buri then false
        else true)
      buri_to_remove
  in
  (* now calculate the list of objects that belong to these baseuris *)
  let uri_to_remove = 
    try
      List.fold_left 
        (fun acc buri ->
          let inhabitants = HG.ls ~local:true (buri ^ "/") in
          let inhabitants = List.filter 
              (function HGT.Ls_object _ -> true | _ -> false) 
            inhabitants
          in
          let inhabitants = List.map 
              (function 
               | HGT.Ls_object e -> buri ^ "/" ^ e.HGT.uri 
               | _ -> assert false)
            inhabitants
          in
          inhabitants @ acc)
      [] buri_to_remove 
    with HGT.Invalid_URI u -> 
      HLog.error ("We were listing an invalid buri: " ^ u);
      exit 1
  in
  let uri_to_remove_from_db =
   List.fold_left 
     (fun acc buri -> 
       let dbu = db_uris_of_baseuri buri in
       dbu @ acc
     ) [] buri_to_remove 
  in
  let uri_to_remove = uri_to_remove @ uri_to_remove_from_db in
  let uri_to_remove =
   HExtlib.list_uniq (List.sort Pervasives.compare uri_to_remove) in
  (* now we want the list of all uri that depend on them *) 
  let depend = 
    List.fold_left
    (fun acc u -> one_step_depend cache_of_processed_baseuri u dbtype dbd @ acc)
    [] uri_to_remove
  in
  let depend = 
    HExtlib.list_uniq (List.fast_sort Pervasives.compare depend) 
  in
  uri_to_remove, depend
;;

let rec close_db cache_of_processed_baseuri uris next =
  match next with
  | [] -> uris
  | l -> 
     let uris, next = close_uri_list cache_of_processed_baseuri l in
     close_db cache_of_processed_baseuri uris next @ uris
;;
  
let cleaned_no = ref 0;;

  (** TODO repellent code ... *)
let moo_root_dir = lazy (
  let url =
    List.assoc "cic:/matita/"
      (List.map
        (fun pair ->
          match
            Str.split (Str.regexp "[ \t\r\n]+") (HExtlib.trim_blanks pair)
          with
          | a::b::_ -> a, b
          | _ -> assert false)
        (Helm_registry.get_list Helm_registry.string "getter.prefix"))
  in
  String.sub url 7 (String.length url - 7))
;;
*)

let rec close_db cache_of_processed_baseuri uris next =
  uris (* MATITA 1.0 *)
;;

let clean_baseuris ?(verbose=true) buris =
 (* MATITA 1.0 *) () (*
  let cache_of_processed_baseuri = Hashtbl.create 1024 in
  let buris = List.map Http_getter_misc.strip_trailing_slash buris in
  debug_prerr "clean_baseuris called on:";
  if debug then
    List.iter debug_prerr buris; 
  let l = close_db cache_of_processed_baseuri [] buris in
  let l = HExtlib.list_uniq (List.fast_sort Pervasives.compare l) in
  let l = List.map NUri.uri_of_string l in
  debug_prerr "clean_baseuri will remove:";
  if debug then
    List.iter (fun u -> debug_prerr (NUri.string_of_uri u)) l; 
  List.iter
   (fun baseuri ->
     !decompile ~baseuri;
     try 
      let lexiconfile =
       LibraryMisc.lexicon_file_of_baseuri 
        ~must_exist:false ~writable:true ~baseuri
      in
       HExtlib.safe_remove lexiconfile;
       HExtlib.rmdir_descend (Filename.chop_extension lexiconfile)
     with Http_getter_types.Key_not_found _ -> ())
   (HExtlib.list_uniq (List.fast_sort Pervasives.compare
     (List.map NUri.baseuri_of_uri l @ buris)))
*)
