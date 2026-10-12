let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

(* Three type parameters, A, B and C, all arguments of the type of the bound
   variables, written ["term"; "A"; "B"; "C"] *)

type tctx = Entry of (string[@elpi.key ["term"; "A"; "B"; "C"]])
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

type ('a, 'b, 'c) term =
  | Var of string [@elpi.var tctx]
  | Const of 'a
  | Tag of 'b * ('a, 'b, 'c) term
  | Pair of 'c * 'a
  | Lam of string *
      (('a, 'b, 'c) term[@elpi.binder ["term"; "A"; "B"; "C"] tctx
         (fun s -> Entry s)])
[@@deriving show, elpi { declaration }]

let in_ctx_for_term :
    (ctx_for_term, 'csts)
      ContextualConversion.ctx_readback = in_ctx_for_term

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

(* The copy functions of the three parameters are different *)
let program = {|
func inc int -> int.
inc X Y :- Y is X + 1.

main :-
  term.copy inc string.copy bool.copy
    (lam "x" x\ tag "t" (lam "y" y\ pair tt 1)) T,
  T = lam "x" x\ tag "t" (lam "y" y\ pair tt 2).
|}

let () = Ppx_tests_lib.run_program builtin program
