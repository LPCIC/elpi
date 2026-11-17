open Test_lsp_lib

(* accumulate "+pkg" and "+pkg/path", with packages found by findlib in
   pkgs/ (see dune): the plugin is not loaded, its stub is read *)
let () = register ~name:"pkgs" "pkgs.elpi" (fun file ->
  open_file file;
  hover file "lsp.f 3" 0;
  definition file "lsp.f 3" 0;
  definition file "util.five M" 0)
