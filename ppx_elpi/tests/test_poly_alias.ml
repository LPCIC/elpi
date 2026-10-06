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

let () = Ppx_tests_lib.check_declarations builtin
