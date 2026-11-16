open Test_lsp_lib

(* elpi-lsp -debug FILE: the project of FILE (an entry of its elpi.toml left
   out) and its diagnostics, printed in the terminal *)
let () = register ~name:"debug" "recoverproj/main.elpi" (fun file -> debug file)
