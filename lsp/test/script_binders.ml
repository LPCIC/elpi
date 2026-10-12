open Test_lsp_lib

let () = register ~name:"binders" "binders.elpi" (fun file ->
  open_file file;
  section "variables of the rule, in the head and in the body";
  highlight file "p X Y" 2;
  highlight file "z X" 2;
  definition file "z X" 2;
  section "a variable of another rule";
  highlight file "r X" 2;
  section "pi";
  highlight file "pi z" 3;
  highlight file "q z" 2;
  definition file "q z" 2;
  hover file "q z" 2;
  section "sigma";
  highlight file "r W" 2;
  definition file "r W" 2;
  section "a data binder";
  highlight file "b = a" 0;
  highlight file "a\\ b" 0;
  definition file "= a" 2;
  hover file "= a" 2;
  section "a whole expression: the cursor is on a blank";
  hover file "q z X" 1;
  (* a long term is shortened in the middle *)
  hover file "std.map [Y]" 7;
  section "the type of a quantifier";
  hover file "pi z" 0;
  section "a constant: its declaration and its uses";
  highlight file "q z X" 0;
  highlight file "p X _" 0;
  section "a constant of the standard library: no declaration in the file";
  highlight file "std.map" 1;
  section "not a variable or a constant";
  highlight file "X, sigma" 1;
  hover file "std.map" 1;
  section "semantic tokens";
  semantic_tokens file)
