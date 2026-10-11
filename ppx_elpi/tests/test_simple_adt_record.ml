let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

type simple = K1 of { f : int; g : bool } | K2 of { f2 : bool }
[@@deriving show, elpi { declaration }]

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let program = {|
main :-
  simple.copy (k1 1 tt) X, X = k1 1 tt,
  simple.copy (k2 ff) Y, Y = k2 ff.
|}

let () = Ppx_tests_lib.run_program builtin program
