open Test_lsp_lib

(* an entry of elpi.toml that is wrong (use of a package that is not
   installed) is shown at the start of the document, and left out: the
   paths of the project still count, rp.lib/ten is found *)
let () = register ~name:"recoverproj" "recoverproj/main.elpi" (fun file ->
  open_file file;
  definition file "rp.ten N" 0)
