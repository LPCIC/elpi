let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

(* Pairs, triples and quadruples, options and lists, nested, as the fields of
   a constructor and as type abbreviations *)

type color = Red | Green
[@@deriving show, elpi { declaration }]

type t =
  | P of int * (string * bool)
  | T of int * string * color
  | Q of int * string * color * bool
  | O of color option list
[@@deriving show, elpi { declaration }]

type tr = int * string * color
[@@deriving show, elpi { declaration }]

type qd = int * string * color * bool
[@@deriving show, elpi { declaration }]

let t : 'c 'csts. (t, 'c, 'csts) ContextualConversion.t = t

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let () = Ppx_tests_lib.check_declarations builtin
