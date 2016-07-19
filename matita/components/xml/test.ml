(* $Id: test.ml 5769 2006-01-08 18:00:22Z sacerdot $ *)

(* Parsing test:
 * - XmlPushParser version *)
open Printf
open XmlPushParser

let print s = print_endline s; flush stdout

let callbacks =
  { default_callbacks with
      start_element =
        Some (fun tag attrs ->
          let length = List.length attrs in
          print (sprintf "opening %s [%s]"
            tag (String.concat ";" (List.map fst attrs))));
      end_element = Some (fun tag -> print ("closing " ^ tag));
      character_data = Some (fun data -> print "character data ...");
  }

let xml_parser = create_parser callbacks

let is_gzip f =
  try
    let len = String.length f in
    String.sub f (len - 3) 3 = ".gz"
  with Invalid_argument _ -> false

let _ =
  let xml_source =
    if is_gzip Sys.argv.(1) then
      `Gzip_file Sys.argv.(1)
    else
      `File Sys.argv.(1)
  in
  parse xml_parser xml_source

(* Parsing test:
 * - Pure expat version (without XmlPushParser mediation).
 * Originally written only to test if XmlPushParser mediation caused overhead.
 * That was not the case. *)

(*let _ =*)
(*  let ic = open_in Sys.argv.(1) in*)
(*  let expat_parser = Expat.parser_create ~encoding:None in*)
(*  Expat.set_start_element_handler expat_parser*)
(*    (fun tag attrs ->*)
(*      let length = List.length attrs in*)
(*      print (sprintf "opening %s [%d attribute%s]"*)
(*      tag length (if length = 1 then "" else "s")));*)
(*  Expat.set_end_element_handler expat_parser*)
(*    (fun tag -> print ("closing " ^ tag));*)
(*  Expat.set_character_data_handler expat_parser*)
(*    (fun data -> print "character data ...");*)
(*  try*)
(*    while true do*)
(*      Expat.parse expat_parser (input_line ic ^ "\n")*)
(*    done*)
(*  with End_of_file -> Expat.final expat_parser*)

