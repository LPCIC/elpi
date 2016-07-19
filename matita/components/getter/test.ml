(* $Id: test.ml 5769 2006-01-08 18:00:22Z sacerdot $ *)

let _ = Helm_registry.load_from "foo.conf.xml"
let fname = Http_getter.getxml ~format:`Normal ~patch_dtd:true Sys.argv.(1) in
let ic = open_in fname in
(try
  while true do
    let line = input_line ic in
    print_endline line
  done
with End_of_file -> ())

