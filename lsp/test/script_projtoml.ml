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

(* an elpi.toml that changes while the document is open: the document is
   checked again with it. The files are written here: the ones of dune are
   read-only *)
let () = register ~name:"tomledit" "tomledit/main.elpi" (fun file ->
  (* with /, also on Windows: the name is in the expected output *)
  let toml = Filename.dirname file ^ "/elpi.toml" in
  write_watched_file file "main.\n";
  write_watched_file toml "name = \"tomledit\"\n";
  open_file file;
  write_watched_file toml "name = \"tomledit\"\nnot a key\n";
  await_diagnostics [ file ];
  write_watched_file toml "name = \"tomledit\"\n";
  await_diagnostics [ file ])
