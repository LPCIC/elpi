open Test_lsp_lib

(* a prefix of [paths] in proj/elpi.toml: "lsp.lib/util" is lib/util.elpi *)
let () = register ~name:"projprefix" "proj/src/prefixed.elpi" (fun file ->
  open_file file;
  definition file "util.seven N" 0)
