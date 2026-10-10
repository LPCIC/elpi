let file_name = Sys.argv.(1)

open Elpi.API

(* Two constructors with the same name in two types, with different variants *)

let declaration = PPX.empty_declaration ()

type t1 = A of int [@elpi.variant 1]
[@@deriving show, elpi { declaration }]

type t2 = A of string [@elpi.variant 2]
[@@deriving show, elpi { declaration }]

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

(* Both constructors are called a, the type tells which one is meant *)
let program = {|
main :-
  t1.copy (a 1) X, X = a 1,
  t2.copy (a "s") Y, Y = a "s".
|}

let () = Ppx_tests_lib.run_program builtin program
