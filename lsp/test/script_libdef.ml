open Test_lsp_lib

(* The builtins declared in OCaml are in the text of the library, some before
   and some after the code of the library files (which start with a #line
   directive): their locations are inside the generated files, not at their end *)
let () = register ~name:"libdef" "libdef.elpi" (fun file ->
  open_file file;
  definition file "print" 0;
  definition file "trace.counter" 0)
