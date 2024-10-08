let declaration = ref []

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

let pp_tyctx _ _ = ()
type tyctx = TEntry of (string[@elpi.key]) * bool
[@@elpi.index (module String)]
[@@deriving elpi { declaration }]


let pp_ty _ _ = ()
type ty =
  | TVar of string [@elpi.var tyctx]
  | TApp of string * ty
  | TAll of bool * string * (ty[@elpi.binder tyctx (fun b s -> TEntry(s,b))])
[@@deriving elpi { declaration; }]



let pp_tctx _ _ = ()
type tctx = Entry of (string[@elpi.key]) * ty
[@@elpi.index (module String)]
[@@deriving elpi { declaration ; context = [tyctx]} ]


let pp_term _ _ = ()
type term =
  | Var of string [@elpi.var tctx]
  | App of term * term
  | Lam of ty * string * (term[@elpi.binder tctx (fun b s -> Entry(s,b))])
[@@deriving elpi { declaration }]

let _ =
   fun (f : #ctx_for_tctx -> unit) ->
   fun (x : ctx_for_term) ->
     f x


open Elpi.API
open BuiltInPredicate
open Notation

let term_to_string = CPred("term->string",in_ctx_for_term,
  CIn(term,"T",
  COut(BuiltInContextualData.string,"S",
  CRead("what else"))),
  fun (t : term) (_ety : string oarg)
    ~depth:_ c (_cst : Data.constraints) (_state : State.t) ->

    !: (Format.asprintf "@[<hov>%a@ ; %a@ |-@ %a@]@\n%!"
      (RawData.Constants.Map.pp (ContextualConversion.pp_ctx_entry pp_tctx)) c#tyctx
      (RawData.Constants.Map.pp (ContextualConversion.pp_ctx_entry pp_tctx)) c#tctx
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
  let _elpi = Setup.init ~builtins:[builtin1;builtin2] () in
  BuiltIn.document_file builtin2;
  exit 0
;;
main ()
