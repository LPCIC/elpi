

let output_stanzas filename =
  let base = Filename.remove_extension filename in
  Printf.printf {|
(rule
 (targets %s.actual.ml)
 (deps (:pp pp.exe) (:input %s.ml))
 (action (run ./%%{pp} -deriving-keep-w32 both --impl %%{input} -o %%{targets})))

(rule
 (alias runtest)
 (action (diff %s.expected.ml %s.actual.ml)))

(rule
 (alias runtest)
 (action (diff %s.expected.elpi %s.actual.elpi)))

(rule
  (target %s.actual.elpi)
  (action (run ./%s.exe %%{target})))

(executable
  (name %s)
  (modules %s)
  (preprocess (pps elpi.ppx)))

|}
  base base base base base base base base base base

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