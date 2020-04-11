let elpi_stuff = ref []

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show x = x
end

let pp_tctx _ _ = ()
type tctx = TDecl of (string[@elpi.key]) * bool
[@@deriving elpi { index = (module String) ; declaration = elpi_stuff } ]

let pp_tye _ _ = ()
type tye =
  | TVar of string [@elpi.var]
  | TConst of string
  | TArrow of tye * tye
[@@deriving elpi { context = (x : (tye -> tctx) ) ; declaration = elpi_stuff  } ]

let pp_ty _ _ = ()
type ty =
  | Mono of tye
  | Forall of string * bool * (ty[@elpi.binder tye (fun s b -> TDecl(s,b))])
[@@deriving elpi { context = (x : (tye -> tctx) * (ty -> tctx)) }]

let pp_ctx _ _ = ()
type ctx = Decl of (string[@elpi.key]) * ty
[@@deriving elpi { index = (module String); context = (x : tctx) ; declaration = elpi_stuff  } ]

type term =
  | Var of string [@elpi.var]
  | App of term list [@elpi.code "appl"] [@elpi.doc "bla bla"]
  | Lam of string * ty * (term[@elpi.binder term (fun s ty -> Decl(s,ty))])
  | Literal of int [@elpi.skip]
  | Cast of term * ty
      (* Example: override the embed and readback code for this constructor *)
      [@elpi.embed fun default ~depth hyps constraints state a1 a2 ->
        default ~depth hyps constraints state a1 a2 ]
      [@elpi.readback fun default ~depth hyps constraints state l ->
         default ~depth hyps constraints state l ]
      [@elpi.code "type-cast" "term -> ty -> term"]
[@@deriving elpi { context = (x : (ty -> tctx) * (term -> ctx)) } ]
[@@elpi.pp let rec aux fmt = function
   | Var s -> Format.fprintf fmt "%s" s
   | App tl -> Format.fprintf fmt "App %a" (Elpi.API.RawPp.list aux " ") tl
   | Lam(s,ty,t) -> Format.fprintf fmt "Lam %s (%a)" s aux t
   | Literal i -> Format.fprintf fmt "%d" i
   | Cast(t,_) -> aux fmt t
   in aux ]

open Elpi.API
open BuiltInPredicate
open Notation

let term_to_string = Pred("term->string",
  CIn(term,"T",
  COut(ContextualConversion.(!>) BuiltInData.string,"S",
  Read(in_ctx, "what else"))),
  fun (t : term) (_ety : string oarg)
    ~depth:_ ((ctx1,ctx2) : tctx ContextualConversion.ctx_entry RawData.Constants.Map.t * ctx ContextualConversion.ctx_entry RawData.Constants.Map.t)
    (_cst : Data.constraints) (_state : State.t) ->

    !: (Format.asprintf "@[<hov>%a@ %a@ |-@ %a@]@\n%!"
      (RawData.Constants.Map.pp (ContextualConversion.pp_ctx_entry pp_tctx)) ctx1
      (RawData.Constants.Map.pp (ContextualConversion.pp_ctx_entry pp_ctx)) ctx2
       term.pp t)

)

let builtin = let open BuiltIn in
  declare ~file_name:"test_ppx.elpi" (!elpi_stuff @ [
    MLCode(term_to_string,DocAbove);
    LPDoc "----------------- elpi ----------------"
  ] @ Elpi.Builtin.(core_builtins @ elpi_builtins))

let program = {|
main :-
  pi x w y q t\
    tdecl t "alpha" tt =>
    decl y "arg" (forall "ss" tt s\ mono (tarrow (tconst "nat") s)) =>
    decl x "f" (mono (tarrow (tconst "nat") t)) =>
      print {term->string (appl [x, y, lam "zzzz" (mono t) z\ z])}.

|}

let main () =
  let elpi, _ = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  let out = open_out Sys.argv.(1) in
  let fmt = Format.formatter_of_out_channel out in
  Setup.set_err_formatter fmt;
  Setup.set_std_formatter fmt;
  let program = Parse.program_from_stream ~elpi (Ast.Loc.initial "test")
    Stream.(of_string program) in
  let goal = Parse.goal (Ast.Loc.initial "test") "main." in
  let program = Compile.program ~elpi ~flags:Compile.default_flags [program] in
  let goal = Compile.query program goal in
  let exe = Compile.optimize goal in
  match Execute.once exe with
  | Execute.Success _ -> Format.pp_print_flush fmt (); close_out out; exit 0
  | _ -> exit 1
  ;;

main ()