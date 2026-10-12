open Test_lsp_lib

(* errors found by the parts of the runtime used by the compiler (grafting,
   clausify): each one is reported, the other rules are compiled *)
let () = register ~name:"assemble" "assemble.elpi" (fun file ->
  open_file file;
  section "run";
  run ~file "main")
