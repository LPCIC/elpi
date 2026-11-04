open Test_lsp_lib

(* files accumulated from other directories (accdirs/): lang/ast.elpi is
   accumulated by lang/anf.elpi as `ast`, next to it, although anf.elpi is
   reached from a/ as ../lang/anf; and it is accumulated twice, through a.elpi
   and through b.elpi, but loaded once. No error, and the names are found *)
let () = register ~name:"accdirs" "accdirs/main/main.elpi" (fun file ->
  open_file file;
  hover file "fa X Z" 0;
  definition file "fb Z Y" 0)
