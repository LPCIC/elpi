open Test_lsp_lib

(* the plugin preloaded by quoteproj/elpi.toml installs the default
   quotation, and the macros of its prelude are seen: only bad, whose
   quotation is a string, is an error *)
let () = register ~name:"quoteproj" "quoteproj/main.elpi" (fun file ->
  open_file file)
