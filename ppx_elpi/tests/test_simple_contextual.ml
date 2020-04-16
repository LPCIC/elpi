let declaration = ref []

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

let pp_ctx _ _ = ()
type ctx = Entry of (string[@elpi.key]) * bool
  [@@elpi.index (module String)]
[@@deriving elpi { declaration }]

let ctx : (int * ctx, < raw :  Elpi.API.RawData.hyp list; .. >, 'a) Elpi.API.ContextualConversion.t  = ctx
let in_ctx : (ctx, string) Elpi.API.PPX.context = in_ctx

let pp_term _ _ = ()
type term =
  | Var of string [@elpi.var ctx]
  | App of term * term
  | Lam of bool * string * (term[@elpi.binder "term" ctx (fun b s -> Entry(s,b))])
[@@deriving elpi { declaration }]

let term : (term, < ctx : ctx Elpi.API.ContextualConversion.ctx_entry Elpi.API.RawData.Constants.Map.t; .. >, 'a) Elpi.API.ContextualConversion.t  = term
let term_ctx : (< ctx : ctx Elpi.API.ContextualConversion.ctx_entry Elpi.API.RawData.Constants.Map.t >, 'a) Elpi.API.ContextualConversion.ctx_readback =
  fun ~depth h c s ->
    let s, gls = Elpi.API.PPX.readback_context [Elpi.API.PPX.C in_ctx] ~depth h c s in
    s, object method ctx = in_ctx.Elpi.API.PPX.get s end, c, gls

open Elpi.API
open BuiltInPredicate
open Notation

let term_to_string = Pred("term->string",
  CIn(term,"T",
  COut(ContextualConversion.(!>) BuiltInData.string,"S",
  Read(term_ctx, "what else"))),
  fun (t : term) (_ety : string oarg)
    ~depth:_ c (_cst : Data.constraints) (_state : State.t) ->

    !: (Format.asprintf "@[<hov>%a@ |-@ %a@]@\n%!"
      (RawData.Constants.Map.pp (ContextualConversion.pp_ctx_entry pp_ctx)) c#ctx
       term.pp t)

)

let builtin1 = let open BuiltIn in
  declare ~file_name:"test_ppx.elpi" (!declaration @ [
    MLCode(term_to_string,DocAbove);
    LPDoc "----------------- elpi ----------------"
  ] @ Elpi.Builtin.(core_builtins @ elpi_builtins))

let builtin2 = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !declaration

let main () =
  let _elpi, _ = Setup.init ~builtins:[builtin1;builtin2] ~basedir:"." [] in
  BuiltIn.document_file builtin1;
  exit 0
;;

main ()
