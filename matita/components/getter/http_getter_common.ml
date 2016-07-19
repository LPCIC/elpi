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

(* $Id: http_getter_common.ml 6030 2006-02-03 15:15:33Z zacchiro $ *)

open Http_getter_types;;
open Printf;;

let string_of_ls_flag = function No -> "NO" | Yes -> "YES" | Ann -> "ANN"
let string_of_encoding = function
  | `Normal -> "Normal"
  | `Gzipped -> "GZipped"

let is_cic_obj_uri uri = Pcre.pmatch ~pat:"^cic:" uri
let is_theory_uri uri = Pcre.pmatch ~pat:"^theory:" uri
let is_cic_uri uri = is_cic_obj_uri uri || is_theory_uri uri
let is_nuprl_uri uri = Pcre.pmatch ~pat:"^nuprl:" uri
let is_rdf_uri uri = Pcre.pmatch ~pat:"^helm:rdf(.*):(.*)//(.*)" uri
let is_xsl_uri uri = Pcre.pmatch ~pat:"^\\w+\\.xsl" uri

let rec uri_of_string = function
  | uri when is_rdf_uri uri ->
      (match Pcre.split ~pat:"//" uri with
      | [ prefix; uri ] ->
          let rest =
            match uri_of_string uri with
            | Cic_uri xmluri -> xmluri
            | _ -> raise (Invalid_URI uri)
          in
          Rdf_uri (prefix, rest)
      | _ -> raise (Invalid_URI uri))
  | uri when is_cic_obj_uri uri -> Cic_uri (Cic (Pcre.replace ~pat:"^cic:" uri))
  | uri when is_nuprl_uri uri -> Nuprl_uri (Pcre.replace ~pat:"^nuprl:" uri)
  | uri when is_theory_uri uri ->
      Cic_uri (Theory (Pcre.replace ~pat:"^theory:" uri))
  | uri -> raise (Invalid_URI uri)

let patch_xsl ?(via_http = true) () =
  fun line ->
    let mk_patch_fun tag line =
      Pcre.replace
        ~pat:(sprintf "%s\\s+href=\"" tag)
        ~templ:(sprintf "%s href=\"%s/getxslt?uri="
          tag (Lazy.force Http_getter_env.my_own_url))
        line
    in
    let (patch_import, patch_include) =
      (mk_patch_fun "xsl:import", mk_patch_fun "xsl:include")
    in
    patch_include (patch_import line)

let patch_system kind ?(via_http = true) () =
  let rex =
    Pcre.regexp (sprintf "%s (.*) SYSTEM\\s+\"((%s)/)?" kind
      (String.concat "|" (Lazy.force Http_getter_env.dtd_base_urls)))
  in
  let templ =
    if via_http then
      sprintf "%s $1 SYSTEM \"%s/getdtd?uri=" kind
        (Lazy.force Http_getter_env.my_own_url)
    else
      sprintf "%s $1 SYSTEM \"file://%s/" kind (Http_getter_env.get_dtd_dir ())
  in
  fun line -> Pcre.replace ~rex ~templ line

let patch_entity = patch_system "ENTITY"
let patch_doctype = patch_system "DOCTYPE"

let patch_xmlbase =
  let rex = Pcre.regexp "^(\\s*<\\w[^ ]*)(\\s|>)" in
  fun xmlbases baseurl baseuri s ->
    let s' =
      Pcre.replace ~rex
        ~templ:(sprintf "$1 xml:base=\"%s\" helm:base=\"%s\"$2" baseurl baseuri)
        s
    in
    if s <> s' then xmlbases := None;
    s'

let patch_dtd = patch_entity
let patch_xml ?via_http ?xmlbases () =
  let xmlbases = ref xmlbases in
  fun line ->
    match !xmlbases with
    | None -> patch_doctype ?via_http () (patch_entity ?via_http () line)
    | Some (xmlbaseuri, xmlbaseurl) ->
        patch_xmlbase xmlbases xmlbaseurl xmlbaseuri
          (patch_doctype ?via_http () (patch_entity ?via_http () line))

let return_file
  ~fname ?contype ?contenc ?patch_fun ?(gunzip = false) ?(via_http = true)
  ~enc outchan
=
  if via_http then begin
    let headers =
      match (contype, contenc) with
      | (Some t, Some e) -> ["Content-Encoding", e; "Content-Type", t]
      | (Some t, None) -> ["Content-Type" , t]
      | (None, Some e) -> ["Content-Encoding", e]
      | (None, None) -> []
    in
    Http_daemon.send_basic_headers ~code:(`Code 200) outchan;
    Http_daemon.send_headers headers outchan;
    Http_daemon.send_CRLF outchan
  end;
  match gunzip, patch_fun with
  | true, Some patch_fun ->
      Http_getter_logger.log ~level:2
        "Patch required, uncompress/compress cycle needed :-(";
      (* gunzip needed, uncompress file, apply patch_fun to it, compress the
       * result and sent it to client *)
      let (tmp1, tmp2) =
        (Http_getter_misc.tempfile (), Http_getter_misc.tempfile ())
      in
      (try
        Http_getter_misc.gunzip ~keep:true ~output:tmp1 fname; (* gunzip tmp1 *)
        let new_file = open_out tmp2 in
        Http_getter_misc.iter_file  (* tmp2 = patch(tmp1) *)
          (fun line ->
            output_string new_file (patch_fun line ^ "\n");
            flush outchan)
          tmp1;
        close_out new_file;
        Http_getter_misc.gzip ~output:tmp1 tmp2;(* tmp1 = gzip(tmp2); rm tmp2 *)
        Http_getter_misc.iter_file  (* send tmp1 to client as is*)
          (fun line -> output_string outchan (line ^ "\n"); flush outchan)
          tmp1;
        Sys.remove tmp1       (* rm tmp1 *)
      with e ->
        Sys.remove tmp1;
        raise e)
  | false, Some patch_fun ->
      (match enc with
      | `Normal ->
          Http_getter_misc.iter_file
            (fun line -> output_string outchan (patch_fun (line ^ "\n")))
            fname
      | `Gzipped -> assert false)
        (* dangerous case, if this happens it needs to be investigated *)
  | _, None -> Http_getter_misc.iter_file_data (output_string outchan) fname
;;

