open Test_lsp_lib

(* a type error in an accumulated file is shown on the accumulate directive,
   not on the text of a comment that looks like one *)
let () = register ~name:"acctype" "acctype.elpi" (fun file ->
  open_file file)
