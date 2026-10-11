let file_name = Sys.argv.(1)

open Elpi.API

(* A builtin predicate taking two data types: one with binders, whose
   conversion is derived by the ppx, and one without binders, whose conversion
   is written by hand with AlgebraicData *)

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

(* The context, and the datum with binders, derived by the ppx *)

type tctx = Entry of (string[@elpi.key "term"]) * bool
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

type term =
  | Var of string [@elpi.var tctx]
  | App of term * term
  | Lam of bool * string *
      (term[@elpi.binder "term" tctx
         (fun b s -> Entry(s,b))])
[@@deriving show, elpi { declaration }]

let term :
    'c 'csts.
    (term, #ctx_for_term as 'c, 'csts)
      ContextualConversion.t = term
let in_ctx_for_term :
    (ctx_for_term, 'csts)
      ContextualConversion.ctx_readback = in_ctx_for_term

(* The datum without binders, with a hand written conversion *)

type color = Red | Green | Blue of int
[@@deriving show]

let color =
  let open AlgebraicData in
  declare {
    ty = TyName "color";
    doc = "The colours";
    pp = pp_color;
    constructors = [
      K("red","",N,
        B Red,
        M (fun ~ok ~ko -> function Red -> ok | _ -> ko ()));
      K("green","",N,
        B Green,
        M (fun ~ok ~ko -> function Green -> ok | _ -> ko ()));
      K("blue","",A(BuiltInData.int,N),
        B (fun i -> Blue i),
        M (fun ~ok ~ko -> function Blue i -> ok i | _ -> ko ()));
    ]
  }

(* The builtin takes both, in the context of the term *)

open BuiltInPredicate.Notation

let describe = BuiltInPredicate.ContextualPred("describe",in_ctx_for_term,
  In(term,"T",
  In(color,"C",
  Out(BuiltInData.stringC,"S",
  Read("describes a term and a colour")))),
  fun (t : term) (c : color) (_s : string BuiltInPredicate.oarg)
    ~depth:_ ctx (_cst : Data.constraints) (_state : State.t) ->

    !: (Format.asprintf "@[<hov>%a@ ;@ %a@ |-@ %a@]@\n%!"
      color.pp c
      (RawData.Constants.Map.pp
         (PPX.pp_ctx_entry pp_tctx))
        ctx#tctx
       term.pp t)
)

let builtin = let open BuiltIn in
  BuiltIn.declare ~file_name ((PPX.to_list declaration) @ [
    MLDataC color;
    MLCode(describe,DocAbove);
  ])

let program = {|
main :-
  pi x\
    entry x "x" tt ==>
      print {describe (lam tt "y" y\ app x y) (blue 3)}.
|}

let () = Ppx_tests_lib.run_program builtin program
