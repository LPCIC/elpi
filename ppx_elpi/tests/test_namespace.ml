let file_name = Sys.argv.(1)

(* [@@elpi.namespace "ns"]: the constructors with the default Elpi name get
   ns. in front of it; an explicit [@elpi.code] is taken as it is *)

open Elpi.API

let declaration = PPX.empty_declaration ()

type value =
  | Null
  | Number of int
  | Pair of value * value [@elpi.code "pair-of-values"]
[@@elpi.namespace "val"]
[@@deriving show, elpi { declaration }]

type point = { x : int; y : int }
[@@elpi.namespace "geo"]
[@@deriving show, elpi { declaration }]

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let program = {|
main :-
  value.copy (pair-of-values val.null (val.number 1)) X,
  X = pair-of-values val.null (val.number 1),
  point.copy (geo.point 1 2) (geo.point 1 2).
|}

let () = Ppx_tests_lib.run_program builtin program
