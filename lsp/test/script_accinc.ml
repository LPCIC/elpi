open Test_lsp_lib

(* a file accumulated from a directory given to the server with -I (see dune):
   no error, and its predicates are found *)
let () = register ~name:"accinc" "accinc.elpi" (fun file ->
  open_file file;
  hover file "inclib X" 0;
  definition file "inclib X" 0)
