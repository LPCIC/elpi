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

(* $Id: hMarshal.ml 7703 2007-09-23 12:27:52Z fguidi $ *)

exception Corrupt_file of string
exception Format_mismatch of string
exception Version_mismatch of string

let ensure_path_exists fname = HExtlib.mkdir (Filename.dirname fname)
let marshal_flags = []

let save ~fmt ~version ~fname data =
  ensure_path_exists fname;
  let oc = open_out fname in
  let marshalled = Marshal.to_string data marshal_flags in
  output_binary_int oc (Hashtbl.hash fmt);        (* field 1 *)
  output_binary_int oc version;                   (* field 2 *)
  output_string oc fmt;                           (* field 3 *)
  output_string oc (string_of_int version);       (* field 4 *)
  output_binary_int oc (Hashtbl.hash marshalled); (* field 5 *)
  output_string oc marshalled;                    (* field 6 *)
  close_out oc;
  HExtlib.chmod 0o664 fname

let expect ic fname s =
  let len = String.length s in
  let buf = String.create len in
  really_input ic buf 0 len;
  if buf <> s then raise (Corrupt_file fname)

let load ~fmt ~version ~fname =
  let ic = open_in fname in
  HExtlib.finally
    (fun () -> close_in ic)
    (fun () ->
      try
        let fmt' = input_binary_int ic in         (* field 1 *)
        if fmt' <> Hashtbl.hash fmt then raise (Format_mismatch fname);
        let version' = input_binary_int ic in     (* field 2 *)
        if version' <> version then raise (Version_mismatch fname);
        expect ic fname fmt;                      (* field 3 *)
        expect ic fname (string_of_int version);  (* field 4 *)
        let checksum' = input_binary_int ic in    (* field 5 *)
        let marshalled' = HExtlib.input_all ic in (* field 6 *)
        if checksum' <> Hashtbl.hash marshalled' then
          raise (Corrupt_file fname);
        Marshal.from_string marshalled' 0
      with End_of_file -> raise (Corrupt_file fname))
    ()

