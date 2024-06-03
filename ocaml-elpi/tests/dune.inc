
(rule
 (targets test_swap.actual.ml)
 (deps (:pp pp.exe) (:input test_swap.ml) ../ocaml_ast.elpi test_swap.elpi)
 (action (run ./%{pp} --impl %{input} --cookie "program=\"test_swap.elpi\"" -o %{targets})))

(rule
 (alias runtest)
 (action (diff test_swap.expected.ml test_swap.actual.ml)))

(executable
  (name test_swap)
  (modules test_swap)
  (preprocess (pps ocaml-elpi.ppx -- --cookie "program=\"ocaml-elpi/tests/test_swap.elpi\"")))

