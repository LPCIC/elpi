open Test_lsp_lib

(* accumulate "+/path" in a subdirectory of a project (proj/, its elpi.toml
   gives the name): the file at the root of the project *)
let () = register ~name:"proj" "proj/src/main.elpi" (fun file ->
  open_file file;
  definition file "util.seven N" 0)
