let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

(* A polymorphic variant: a tag with no argument, with one argument, with a
   tuple (one argument per component) and with an Elpi name of its own *)
type shape = [ `Dot | `Circle of int | `Rect of int * int | `Hidden of bool [@elpi.code "secret"] ]
[@@deriving show, elpi { declaration }]

(* with a type parameter *)
type 'a tagged = [ `Plain | `Tag of 'a ]
[@@deriving show, elpi { declaration }]

open BuiltInPredicate.Notation

(* the OCaml side: the tags read back from Elpi and embedded into Elpi *)
let grow = BuiltInPredicate.ContextualPred("grow",
  (fun ~depth:_ hyps constraints state -> state, new PPX.ctx hyps, constraints, []),
  In(shape,"S",
  Out(shape,"T",
  Read("T is S, twice as large"))),
  fun (s : shape) (_ : shape BuiltInPredicate.oarg) ~depth:_ _ _ _ ->
    !: (match s with
        | `Dot -> `Dot
        | `Circle r -> `Circle (2 * r)
        | `Rect (w, h) -> `Rect (2 * w, 2 * h)
        | `Hidden b -> `Hidden (not b)))

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration @ [ BuiltIn.MLCode(grow, BuiltIn.DocAbove) ])

let program = {|
main :-
  shape.copy (rect 1 2) X, X = rect 1 2,
  grow dot dot,
  grow (circle 3) (circle 6),
  grow (rect 1 2) (rect 2 4),
  grow (secret tt) (secret ff),
  tagged.copy shape.copy (tag (circle 1)) Y, Y = tag (circle 1),
  tagged.copy shape.copy plain Z, Z = plain.
|}

let () = Ppx_tests_lib.run_program builtin program
