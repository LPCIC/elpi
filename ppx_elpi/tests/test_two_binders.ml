let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

(* A datum with two binders, of different kinds: Lam binds a term variable
   and TLam binds a type variable (as in System F). Each kind of variable has
   its own context, and the context of term is the merge of the two. The Elpi
   types of the bound variables are term and ty. *)

type tmctx = TmEntry of (string[@elpi.key "term"])
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

type tyctx = TyEntry of (string[@elpi.key "ty"])
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

type term =
  | Var of string [@elpi.var tmctx]
  | App of term * term
  | Lam of string *
      (term[@elpi.binder "term" tmctx
         (fun s -> TmEntry s)])
  | TLam of string *
      (term[@elpi.binder "ty" tyctx
         (fun s -> TyEntry s)])
[@@deriving show, elpi { declaration }]

let term :
    'c 'csts.
    (term, #ctx_for_term as 'c, 'csts)
      ContextualConversion.t = term
let in_ctx_for_term :
    (ctx_for_term, 'csts)
      ContextualConversion.ctx_readback = in_ctx_for_term


open BuiltInPredicate.Notation

(* The context received by the predicate has both a method tmctx and a method
   tyctx *)
let term_to_string = BuiltInPredicate.ContextualPred("term->string",in_ctx_for_term,
  In(term,"T",
  Out(BuiltInData.stringC,"S",
  Read("what else"))),
  fun (x : term) (_s : string BuiltInPredicate.oarg)
    ~depth:_ c (_cst : Data.constraints) (_state : State.t) ->

    !: (Format.asprintf "@[<hov>%a@ ;@ %a@ |-@ %a@]@\n%!"
      (RawData.Constants.Map.pp
         (PPX.pp_ctx_entry pp_tmctx))
        c#tmctx
      (RawData.Constants.Map.pp
         (PPX.pp_ctx_entry pp_tyctx))
        c#tyctx
       term.pp x)
)

let builtin = let open BuiltIn in
  BuiltIn.declare ~file_name (
    (* the type of the bound type variables *)
    LPCode "data ty.\nfunc ty.copy ty -> ty." ::
    (PPX.to_list declaration) @ [
    MLCode(term_to_string,DocAbove);
  ])

let program = {|
main :-
  pi x a\
    tmentry x "x" ==>
    tyentry a "a" ==>
    term.copy x x ==> (
      sigma T C\
        T = (tlam "B" b\ lam "y" y\ app x y),
        print {term->string T},
        % the deep copy goes under both kinds of binders
        term.copy T C,
        print {term->string C}).
|}

let () = Ppx_tests_lib.run_program builtin program
