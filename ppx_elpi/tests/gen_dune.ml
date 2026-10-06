

let output_stanzas filename =
  let base = Filename.remove_extension filename in
  Printf.printf {|
; The output of the ppx and of the test executable is generated in
; %s.generated.* and compared with %s.expected.*, but it is also promoted
; to %s.actual.* (ignored by git) in order to be inspectable even when
; the test fails.

(rule
 (targets %s.generated.ml)
 (deps (:pp pp.exe) (:input %s.ml))
 (action (run ./%%{pp} -deriving-keep-w32 both --impl %%{input} -o %%{targets})))

(rule
 (target %s.generated.elpi)
 (action (run ./%s.exe %%{target})))

(rule
 (mode promote)
 (target %s.actual.ml)
 (action (copy %s.generated.ml %s.actual.ml)))

(rule
 (mode promote)
 (target %s.actual.elpi)
 (action (copy %s.generated.elpi %s.actual.elpi)))

(rule
 (alias runtest-ppx)
 (deps %s.actual.ml %s.actual.elpi)
 (action (diff %s.expected.ml %s.generated.ml)))

(rule
 (alias runtest-ppx)
 (action (diff %s.expected.elpi %s.generated.elpi)))

(executable
  (name %s)
  (modules %s)
  (libraries ppx_tests_lib)
  (preprocess (pps ppx_deriving.show ppx_elpi)))

|}
  base base base base base base base base base base base base base base base base base base base base base

let is_test filename =
  Filename.check_suffix filename ".ml" &&
  not (Filename.check_suffix (Filename.remove_extension filename) ".pp") &&
  not (Filename.check_suffix (Filename.remove_extension filename) ".actual") &&
  not (Filename.check_suffix (Filename.remove_extension filename) ".generated") &&
  not (Filename.check_suffix (Filename.remove_extension filename) ".expected") &&
  Re.Str.string_match (Re.Str.regexp_string "test_") filename 0

let () =
  Sys.readdir "."
  |> Array.to_list
  |> List.sort String.compare
  |> List.filter is_test
  |> List.iter output_stanzas