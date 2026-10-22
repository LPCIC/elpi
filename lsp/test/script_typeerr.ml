open Test_lsp_lib

let () = register ~name:"typeerr" "typeerr.elpi" (fun file ->
  open_file file;
  section "semantic tokens";
  semantic_tokens file)
