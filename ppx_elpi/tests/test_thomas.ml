let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

type rat = { num: int; den: int }
[@@deriving show, elpi { declaration }]

type poly =
| Const of rat
| Var of int [@elpi.code "variable"] (* var is an elpi builtin *)
| Add of poly * poly
| Mul of poly * poly
[@@deriving show, elpi { declaration }]

type monomial = { coef: rat; exps: (int * int) list }
[@@deriving show, elpi { declaration }]

type mpoly = monomial list
[@@deriving show, elpi { declaration }]

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let () = Ppx_tests_lib.check_declarations builtin