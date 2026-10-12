let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

(* Two type parameters, A and B, both are arguments of the type of the bound
   variables, written ["term"; "A"; "B"] *)

type tctx = Entry of (string[@elpi.key ["term"; "A"; "B"]])
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

type ('a, 'b) term =
  | Var of string [@elpi.var tctx]
  | Const of 'a
  | Tag of 'b * ('a, 'b) term
  | Lam of string *
      (('a, 'b) term[@elpi.binder ["term"; "A"; "B"] tctx
         (fun s -> Entry s)])
[@@deriving show, elpi { declaration }]

let in_ctx_for_term :
    (ctx_for_term, 'csts)
      ContextualConversion.ctx_readback = in_ctx_for_term

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

(* The copy functions of the two parameters are different *)
let program = {|
func inc int -> int.
inc X Y :- Y is X + 1.

main :-
  term.copy inc string.copy
    (lam "x" x\ tag "t" (lam "y" y\ const 1)) T,
  T = lam "x" x\ tag "t" (lam "y" y\ const 2).
|}

let () = Ppx_tests_lib.run_program builtin program
