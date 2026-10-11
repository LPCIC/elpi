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

let program = {|
main :-
  x.copy (pr (located 1 (b "s" tt)) 2) X,
  X = pr (located 1 (b "s" tt)) 2.
|}

let () = Ppx_tests_lib.run_program builtin program
