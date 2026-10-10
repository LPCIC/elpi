let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

type tyctx = TEntry of (string[@elpi.key "ty"]) * bool
[@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]


type ty =
  | TVar of string [@elpi.var tyctx]
  | TApp of string * ty
  | TAll of bool * string *
      (ty[@elpi.binder tyctx
         (fun b s -> TEntry(s,b))])
[@@deriving show, elpi { declaration; }]



type tctx = Entry of (string[@elpi.key "term"]) * ty
[@@elpi.index (module String)]
[@@deriving show, elpi { declaration; context = [tyctx]} ]


type term =
  | Var of string [@elpi.var tctx]
  | App of term * term
  | Lam of ty * string *
      (term[@elpi.binder tctx
         (fun b s -> Entry(s,b))])
[@@deriving show, elpi { declaration }]

let _ =
   fun (f : #ctx_for_tctx -> unit) ->
   fun (x : ctx_for_term) ->
     f x


open BuiltInPredicate.Notation

let term_to_string = BuiltInPredicate.ContextualPred("term->string",in_ctx_for_term,
  In(term,"T",
  Out(BuiltInData.stringC,"S",
  Read("what else"))),
  fun (t : term) (_ety : string BuiltInPredicate.oarg)
    ~depth:_ c (_cst : Data.constraints) (_state : State.t) ->

    !: (Format.asprintf "@[<hov>%a@ ; %a@ |-@ %a@]@\n%!"
      (RawData.Constants.Map.pp
         (PPX.pp_ctx_entry pp_tyctx))
        c#tyctx
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
