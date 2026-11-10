open Test_lsp_lib

(* the section [warnings] of warnproj/elpi.toml: the linear variable is not
   shown, the undeclared global q is an error *)
let () = register ~name:"warnproj" "warnproj/main.elpi" (fun file ->
  open_file file)
