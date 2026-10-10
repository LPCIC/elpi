let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

type simple = K1 of { f : int; g : bool } | K2 of { f2 : bool }
[@@deriving show, elpi { declaration }]

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let () = Ppx_tests_lib.check_declarations builtin
