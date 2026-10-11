let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

type simple = A | B of int * mut
and mut = C | D of simple
[@@deriving show, elpi { declaration }]

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let program = {|
main :-
  simple.copy (b 1 (d (b 2 c))) X,
  X = b 1 (d (b 2 c)),
  mut.copy (d a) Y, Y = d a.
|}

let () = Ppx_tests_lib.run_program builtin program
