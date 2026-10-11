let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

type simple = { f : int; g : bool }
[@@deriving show, elpi { declaration }]

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let program = {|
main :-
  simple.copy (simple 1 tt) X, X = simple 1 tt.
|}

let () = Ppx_tests_lib.run_program builtin program
