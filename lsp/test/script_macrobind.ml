open Test_lsp_lib

(* a lambda given to a macro, @pi-decl N (a\ ... a ...): its variable is
   hovered and defined at its binder, as without the macro *)
let () = register ~name:"macrobind" "macrobind.elpi" (fun file ->
  open_file file;
  hover file "1 (a" 0;
  hover file "q a" 2;
  definition file "q a" 2;
  section "semantic tokens";
  semantic_tokens file)
