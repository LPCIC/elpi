let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

(* The type of the bound variables of a polymorphic type is term A, written
   ["term"; "A"], where A, B, ... are the names of the type parameters *)

type tctx = Entry of (string[@elpi.key ["term"; "A"]])
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

type 'a term =
  | Var of string [@elpi.var tctx]
  | Const of 'a
  | Lam of string *
      ('a term[@elpi.binder ["term"; "A"] tctx (fun s -> Entry s)])
[@@deriving show, elpi { declaration }]

let in_ctx_for_term :
    (ctx_for_term, 'csts)
      ContextualConversion.ctx_readback = in_ctx_for_term

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let program = {|
main :-
  term.copy int.copy (lam "x" x\ lam "y" y\ const 1) T,
  T = lam "x" x\ lam "y" y\ const 1.
|}

let () = Ppx_tests_lib.run_program builtin program
