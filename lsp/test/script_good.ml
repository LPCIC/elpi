open Test_lsp_lib

let () = register ~name:"good" "good.elpi" (fun file ->
  open_file file;
  section "semantic tokens";
  semantic_tokens file;
  section "hover and definition in %s" file;
  hover file "double 3" 0;
  (* the type of a declaration is written with the syntax of the declarations *)
  hover file "double int" 0;
  hover file "double 3 Y" 9;
  hover file "twice Y Z" 0;
  hover file "x\\ y\\ y = x" 6;
  hover file "std.map" 4;
  hover file "\"λ\" L" 5;
  hover file "% a comment" 3;
  (* an expression that ends with a variable is not about that variable *)
  hover file "X * 2" 1;
  hover file "X * 2" 4;
  definition file "double 3" 2;
  definition file "twice Y Z" 1;
  definition file "double 3 Y" 9;
  (* the standard library is a file that the server generates *)
  definition file "std.map" 4;
  (* and so is the text of the builtins written in OCaml *)
  definition file "print \"" 1;
  (* an edit breaking the file, then fixing it *)
  let text = read_file file in
  change_file file 2 (text ^ "oops :- .\n");
  hover file "double 3" 0;
  change_file file 3 text;
  hover file "double 3" 0;
  (* a burst of changes is checked once, at the end *)
  change_file_burst file 4 [ text ^ "oops :- .\n"; text ^ "oops2 :- .\n"; text ];
  hover file "double 3" 0)
