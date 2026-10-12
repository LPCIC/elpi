open Test_lsp_lib

(* the uses of a macro are one token for the name, also when it has arguments *)
let () = register ~name:"macros" "macros.elpi" (fun file ->
  open_file file;
  section "semantic tokens";
  semantic_tokens file)
