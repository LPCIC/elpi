open Test_lsp_lib

(* a character that the lexer does not know, in an accumulated file: the
   error is in that file, the document is parsed on *)
let () = register ~name:"accchar" "accchar.elpi" (fun file ->
  open_file file)
