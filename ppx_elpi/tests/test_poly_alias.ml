let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

type 'a simple = 'a * int
[@@deriving show, elpi { declaration }]

let simple :
    'a 'c 'csts.
    ('a, 'c, 'csts) ContextualConversion.t ->
    ('a simple, 'c, 'csts) ContextualConversion.t = simple

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let program = {|
main :-
  simple.copy int.copy (pr 1 2) X, X = pr 1 2.
|}

let () = Ppx_tests_lib.run_program builtin program
