let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show x = x
end

type tctx = TDecl of (string[@elpi.key "tye"]) * bool
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration } ]

type tye =
  | TVar of string [@elpi.var tctx]
  | TConst of string
  | TArrow of tye * tye
[@@deriving show, elpi { declaration } ]

let tye :
    'a 'csts.
    (tye, #ctx_for_tye as 'a, 'csts)
      ContextualConversion.t = tye
 
type ty =
  | Mono of tye
  | Forall of string * bool *
      (ty[@elpi.binder "tye" tctx
         (fun s b -> TDecl(s,b))])
[@@deriving show, elpi { declaration } ]

let ty :
    'a 'csts.
    (ty, #ctx_for_ty as 'a, 'csts)
      ContextualConversion.t = ty

type ctx = Decl of (string[@elpi.key "term"]) * ty
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration; context = [tctx] } ]

type term =
  | Var of string [@elpi.var ctx]
  | App of term list [@elpi.code "appl"] [@elpi.doc "bla bla"]
  | Lam of string * ty *
      (term[@elpi.binder ctx
         (fun s ty -> Decl(s,ty))])
  | Literal of int [@elpi.skip]
  | Cast of term * ty
      (* Example: override the embed and readback code for this constructor *)
      [@elpi.embed fun default ~depth hyps constraints state a1 a2 ->
         default ~depth hyps constraints state a1 a2 ]
      [@elpi.readback fun default ~depth hyps constraints state l ->
         default ~depth hyps constraints state l ]
      [@elpi.code "type-cast" "term -> ty -> term"]
[@@deriving elpi { declaration; context = [ tctx ; ctx ] } ]
[@@elpi.pp let rec aux fmt = function
   | Var s -> Format.fprintf fmt "%s" s
   | App tl -> Format.fprintf fmt "App %a" (RawPp.list aux " ") tl
   | Lam(s,ty,t) -> Format.fprintf fmt "Lam %s (%a)" s aux t
   | Literal i -> Format.fprintf fmt "%d" i
   | Cast(t,_) -> aux fmt t
   in aux ]

let term :
    'a 'csts.
    (term, #ctx_for_term as 'a, 'csts)
      ContextualConversion.t = term

open BuiltInPredicate.Notation

let term_to_string = BuiltInPredicate.ContextualPred("term->string",in_ctx_for_term,
  In(term,"T",
  Out(BuiltInData.stringC,"S",
  Read("what else"))),
  fun (t : term) (_ety : string BuiltInPredicate.oarg)
    ~depth:_ c (_cst : Data.constraints) (_state : State.t) ->

    !: (Format.asprintf "@[<hov>%a@ %a@ |-@ %a@]@\n%!"
      (RawData.Constants.Map.pp
         (PPX.pp_ctx_entry pp_tctx))
        c#tctx
      (RawData.Constants.Map.pp
         (PPX.pp_ctx_entry pp_ctx))
        c#ctx
       term.pp t)

)

let builtin = let open BuiltIn in
  BuiltIn.declare ~file_name ((PPX.to_list declaration) @ [
    MLCode(term_to_string,DocAbove);
  ])

let program = {|
main :-
  pi x w y q t\
    tdecl t "alpha" tt ==>
    decl y "arg" (forall "ss" tt s\ mono (tarrow (tconst "nat") s)) ==>
    decl x "f" (mono (tarrow (tconst "nat") t)) ==>
    % the bound variables are copied to themselves
    tye.copy t t ==> term.copy x x ==> term.copy y y ==> (
      sigma T C\
        T = (appl [x, y, lam "zzzz" (mono t) z\ z]),
        print {term->string T},
        term.copy T C,
        print {term->string C}).
|}

let () = Ppx_tests_lib.run_program builtin program
