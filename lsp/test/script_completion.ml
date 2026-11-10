open Test_lsp_lib

(* completion: the full names of the symbols of the program, and the short
   names valid at the cursor (in a namespace, after shorten); only the
   segment after the last dot is completed *)
let () = register ~name:"completion" "completion.elpi" (fun file ->
  open_file file;
  (* the members of namespace std, and its namespaces *)
  completion file "std.map []" 4 ~only:[ "map"; "mem"; "string"; "std" ];
  completion file "std.map []" 6 ~only:[ "map"; "map2"; "mem" ];
  (* a symbol of the document, with its documentation; a symb constant *)
  completion file "double 1" 3;
  completion file "red) L" 2;
  (* a namespace of the document, by its full name *)
  completion file "foo.bar 2" 4;
  (* in the namespace, the short names of the symbols that it declares *)
  completion file "bar 1 _" 2 ~only:[ "bar"; "baz" ];
  completion file "baz.qux" 4;
  (* another block of the same namespace does not declare bar *)
  completion file "foo.bar 3" 0 ~only:[ "foo"; "bar"; "other" ];
  (* after shorten std.{ map }, map is std.map *)
  completion file "map [1]" 2 ~only:[ "map" ];
  (* types, macros *)
  completion file "color." 3 ~only:[ "color" ];
  completion file "@twice" 3;
  (* a variable, the full stop of a rule: nothing *)
  completion file "L :-" 1;
  completion file "@twice true." 12;
  (* types, type abbreviations *)
  completion file "int -> int" 2 ~only:[ "int"; "ints" ];
  (* while typing: the rule has a syntax error *)
  let typing = "completion_typing.elpi" in
  open_text typing (read_file file ^ "\nmain :- std.ma");
  completion typing "main :- std.ma" 14 ~only:[ "map"; "map2"; "mem" ];
  completion typing "main :- std.ma" 9 ~only:[ "std" ];
  close_text typing)
