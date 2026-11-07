open Test_lsp_lib

(* the elpi.toml of proj/ is read when the document is opened: its prelude
   (pre.eight) and its paths (found) count; a wrong elpi.toml is an error at
   the start of the document *)
let () = register ~name:"projtoml" "proj/src/uses.elpi" (fun file ->
  open_file file;
  definition file "pre.eight A" 0;
  definition file "found.nine B" 0)

let () = register ~name:"badproj" "badproj/main.elpi" (fun file ->
  open_file file)
