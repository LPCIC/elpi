open Test_lsp_lib

(* spilling, {f X}: the spilled call and its arguments are colored as the
   text says, the variable introduced by the spill is not shown *)
let () = register ~name:"spill" "spill.elpi" (fun file ->
  open_file file;
  section "semantic tokens";
  semantic_tokens file)
