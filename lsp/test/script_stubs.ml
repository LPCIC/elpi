open Test_lsp_lib

(* builtins whose OCaml code is not loaded (stubs) are accepted *)
let () = register ~name:"stubs" "stubs.elpi" (fun file ->
  open_file file;
  hover file "my.say \"" 0;
  hover file "my.tm 3" 0;
  hover file "my.nil :-" 0)
