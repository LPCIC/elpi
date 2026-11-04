open Test_lsp_lib

(* accumulate finds the documents open in the editor before the disk: two
   documents of virtual/, a directory that does not exist (as in the server in
   a browser, which has no disk), a.elpi accumulating b.elpi *)
let a = "virtual/a.elpi"
let b = "virtual/b.elpi"
let b_text = "% vb, declared in b.elpi\npred vb o:int.\nvb 7.\n"

let () = register ~name:"accopen" a (fun a ->
  open_text b b_text;
  await_diagnostics [ b ];
  (* b is checked again when a is opened: an accumulate may find it now *)
  open_text a "accumulate \"b\".\npred main.\nmain :- vb X, Y is X + 1, print Y.\n";
  await_diagnostics [ a; b ];
  hover a "vb X" 0;
  definition a "vb X" 0;
  (* vb has another type: a, which accumulates b, is checked again *)
  change_text b 2 "pred vb o:string.\nvb \"seven\".\n";
  await_diagnostics [ b; a ];
  change_text b 3 b_text;
  await_diagnostics [ b; a ];
  (* a syntax error in b: the error is on the accumulate of a, which still
     depends on b, and is checked again when b is fixed *)
  change_text b 4 "pred vb o:int.\nvb 7 :- .\n";
  await_diagnostics [ b; a ];
  change_text b 5 b_text;
  await_diagnostics [ b; a ];
  (* closed, b is no longer found: there is no file virtual/b.elpi *)
  close_text b;
  await_diagnostics [ b; a ])
