open Test_lsp_lib

(* The request elpi/run: a query on an open document, or on a text (whose
   textDocument is the test directory) *)
let () = register ~name:"run" "run.elpi" (fun file ->
  open_file file;
  run ~file "main";
  run ~file "fails.";
  run ~file "main :- ";                      (* a syntax error in the query *)
  run ~file "undeclared";                    (* undeclared: a warning, and it fails *)
  run ~file:"" ~text:"pred p.\np :- print \"from a text\".\n" "p";
  run ~file:"" ~text:"pred p i:int.\np \"a\".\n" "p 1";  (* a type error in the text *)
  (* a type error: the rule is dropped, the rest of the program runs *)
  run ~file:"" ~text:"pred age -> string, int.\nage \"bob\" 23.\nage \"alice\" 20x.\nmain :- age X Y, print X \"is\" Y, fail.\nmain :- print \"all printed\".\n" "main";
  run ~file:"" ~text:"pred p.\np :- print \"before q\", q.\n" "p";  (* a warning in the text, then it runs *)
  run ~file:"" ~text:"pred p.\np :- print \"before\", std.fatal-error \"boom\".\n" "p";  (* an error while running *)
  (* a success: the values of the variables of the query *)
  run ~file:"" ~text:"pred p o:int, o:list string.\np 3 [\"a\", \"b\"].\n" "p N L";
  (* a success that leaves constraints *)
  run ~file:"" ~text:"func even int.\neven (uvar as X) :- !, declare_constraint (even X) [X].\npred main.\nmain :- even _, (pi z\\ even z => even Y), print Y.\n" "main";
  run ~text:"pred p.\np.\n" "p";            (* no textDocument *)
  run "main";                                (* neither a document nor a text *)
  (* the text is in the test directory: accumulate finds lib.elpi there *)
  run ~file:"" ~text:"accumulate lib.\npred main.\nmain :- twice 2 X, print X.\n" "main";
  run ~file ~max_steps:(`Int 1000) "loop";   (* stopped after 1000 steps *)
  run ~file ~max_steps:(`Int 1000) "main";   (* enough steps *)
  run ~file ~max_steps:(`Int 0) "main";      (* not a positive integer *)
  open_file "good.elpi";                     (* it accumulates lib.elpi *)
  run ~file:"good.elpi" "main";
  close_file "good.elpi")
