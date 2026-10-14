let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

type rat = { num: int; den: int }
[@@deriving show, elpi { declaration }]

type poly =
| Const of rat [@elpi.code "pcst"] (* as in the paper *)
| Var of int [@elpi.code "variable"] (* var is an elpi builtin, not allowed naymore *)
| Add of poly * poly
| Mul of poly * poly
[@@deriving show, elpi { declaration }]
[@@elpi.type_code "polyT"] (* as in the paper *)

type monomial = { coef: rat; exps: (int * int) list }
[@@deriving show, elpi { declaration }]

type mpoly = monomial list
[@@deriving show, elpi { declaration }]

(* check the generated constants have the type we expect *)

let _ : (rat,_,_) ContextualConversion.t = rat
let _ : (poly,_,_) ContextualConversion.t = poly
let _ : (monomial,_,_) ContextualConversion.t = monomial
let _ : (mpoly,_,_) ContextualConversion.t = mpoly


open BuiltInPredicate.Notation

let poly_to_str =
  let open BuiltIn in
  let open BuiltInPredicate in
  MLCode(ContextualPred("poly->str",in_ctx_for_poly,
  In(poly,"P",
  Out(BuiltInData.stringC,"S",
  Read("prints a polynomial"))),
  fun (p : poly) (_s : string BuiltInPredicate.oarg)
    ~depth:_ _ctx (_cst : Data.constraints) (_state : State.t) ->
    !: (show_poly p)),DocAbove)

let builtin = BuiltIn.declare ~file_name ((PPX.to_list declaration) @ [poly_to_str])

let () = Ppx_tests_lib.check_declarations builtin
