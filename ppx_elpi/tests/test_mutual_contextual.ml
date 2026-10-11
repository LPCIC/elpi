let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

type tctx = Entry of (string[@elpi.key "term"])
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

(* Mutually recursive types, the context is shared and the binder is in the
   second type *)
type term =
  | Var of string [@elpi.var tctx]
  | Let of decl * term
  | Unit
and decl =
  | Def of string * (term[@elpi.binder "term" tctx (fun s -> Entry s)])
[@@deriving show, elpi { declaration }]

let term :
    'c 'csts.
    (term, #ctx_for_term as 'c, 'csts)
      ContextualConversion.t = term

let in_ctx_for_term :
    (ctx_for_term, 'csts)
      ContextualConversion.ctx_readback = in_ctx_for_term

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let program = {|
main :-
  term.copy (let (def "x" x\ x) (let (def "y" y\ y) unit)) Y, print Y.
|}

let () = Ppx_tests_lib.run_program builtin program
