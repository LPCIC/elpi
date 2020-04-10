

let output_stanzas filename =
  let base = Filename.remove_extension filename in
  Printf.printf {|
(rule
 (targets %s.actual.ml)
 (deps (:pp pp.exe) (:input %s.ml) ../ocaml_ast.elpi)
 (action (run ./%%{pp} --impl %%{input} --cookie "program=\"%s.elpi\"" -o %%{targets})))

(rule
 (alias runtest)
 (action (diff %s.expected.ml %s.actual.ml)))

(executable
  (name %s)
  (modules %s)
  (preprocess (pps ocaml-elpi.ppx -- --cookie "program=\"ocaml_elpi/tests/%s.elpi\"")))

|}
  base base base base base base base base

let is_test filename =
  Filename.check_suffix filename ".ml" &&
  not (Filename.check_suffix (Filename.remove_extension filename) ".pp") &&
  not (Filename.check_suffix (Filename.remove_extension filename) ".actual") &&
  not (Filename.check_suffix (Filename.remove_extension filename) ".expected") &&
  Re.Str.string_match (Re.Str.regexp_string "test_") filename 0

let () =
  Sys.readdir "."
  |> Array.to_list
  |> List.sort String.compare
  |> List.filter is_test
  |> List.iter output_stanzas