open Test_lsp_lib

(* an anomaly of the compiler (a rule in the position of a goal, after an
   unfinished rule): the unit is dropped and the anomaly is its error; the
   next version is checked as usual *)
let () = register ~name:"anomaly" "anomaly.elpi" (fun file ->
  open_file file;
  section "fixed";
  let text = read_file file in
  change_file file 2 (Str.global_replace (Str.regexp_string "main :- ag\n") "main :- age alice _.\n" text))
