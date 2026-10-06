let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()


type 'a located = {
  loc : int;
  data : 'a;
}
[@@deriving show, elpi { declaration }]

type term =
  | A of int
  | B of string * bool
[@@deriving show, elpi { declaration }]

type x = term located * int
[@@deriving show, elpi { declaration }]

let x :
    'c 'csts.
    (x, 'c, 'csts)
      ContextualConversion.t = x

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let () = Ppx_tests_lib.check_declarations builtin
