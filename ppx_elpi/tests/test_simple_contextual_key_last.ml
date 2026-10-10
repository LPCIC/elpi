let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

(* The key is not the first field of the entry *)
type tctx = Entry of bool * (string[@elpi.key "term"])
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

let tctx :
    'c 'csts.
    (int * tctx, 'c, 'csts)
      ContextualConversion.t = tctx
(* This class is also generated:
     class type ctx_for_tctx = object inherit PPX.ctx end *)
let context_made_of_tctx :
    'c 'csts.
    (tctx, string, #ctx_for_tctx as 'c, 'csts)
      PPX.context = context_made_of_tctx
let in_ctx_for_tctx :
    (ctx_for_tctx, 'csts)
      ContextualConversion.ctx_readback = in_ctx_for_tctx

type term =
  | Var of string [@elpi.var tctx]
  | App of term * term
  | Lam of bool * string *
      (term[@elpi.binder "term" tctx
         (fun b s -> Entry(b,s))])
[@@deriving show, elpi { declaration }]

let term :
    'c 'csts.
    (term, #ctx_for_term as 'c, 'csts)
      ContextualConversion.t = term
let in_ctx_for_term :
    (ctx_for_term, 'csts)
      ContextualConversion.ctx_readback = in_ctx_for_term

open BuiltInPredicate.Notation

let term_to_string = BuiltInPredicate.ContextualPred("term->string",in_ctx_for_term,
  In(term,"T",
  Out(BuiltInData.stringC,"S",
  Read("what else"))),
  fun (t : term) (_ety : string BuiltInPredicate.oarg)
    ~depth:_ c (_cst : Data.constraints) (_state : State.t) ->

    !: (Format.asprintf "@[<hov>%a@ |-@ %a@]@\n%!"
      (RawData.Constants.Map.pp
         (PPX.pp_ctx_entry pp_tctx))
        c#tctx
       term.pp t)

)

let builtin = let open BuiltIn in
  BuiltIn.declare ~file_name ((PPX.to_list declaration) @ [
    MLCode(term_to_string,DocAbove);
  ])

let () = Ppx_tests_lib.check_declarations builtin
