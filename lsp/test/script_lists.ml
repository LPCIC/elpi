open Test_lsp_lib

(* the constants of the syntax of lists are tokens only when they are
   written: [], nil, ::, not the cons and nil of [1, 2] *)
let () = register ~name:"lists" "lists.elpi" (fun file ->
  open_file file;
  section "semantic tokens";
  semantic_tokens file)
