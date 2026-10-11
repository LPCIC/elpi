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

(* Constructors with inline records, one of which has a binder and a variable.
   The attribute of the binder is on the type, hence the parentheses *)
type term =
  | Var of { name : string } [@elpi.var tctx]
  | App of { fun_ : term; arg : term }
  | Lam of { name : string;
             body : (term[@elpi.binder "term" tctx
                        (fun name -> Entry name)]) }
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
  term.copy (lam "x" x\ app x x) Y,
  Y = lam "x" y\ app y y.
|}

let () = Ppx_tests_lib.run_program builtin program
