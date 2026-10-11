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

let program = {|
main :-
  t.copy (p 1 (pr "s" tt)) (p 1 (pr "s" tt)),
  t.copy (t 1 "s" red) (t 1 "s" red),
  t.copy (q 1 "s" green ff) (q 1 "s" green ff),
  t.copy (o [some red, none]) X, X = o [some red, none],
  tr.copy (triple 1 "s" red) (triple 1 "s" red),
  qd.copy (quadruple 1 "s" red tt) (quadruple 1 "s" red tt).
|}

let () = Ppx_tests_lib.run_program builtin program
