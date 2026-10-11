let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

type simple = A | B of int
[@@deriving show, elpi { declaration }]

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let program = {|
main :-
  simple.copy (b 1) X, X = b 1,
  simple.copy a Y, Y = a.
|}

let () = Ppx_tests_lib.run_program builtin program
