open Ast

open Elpi.API
module E  = RawData
module C  = Compile
module Pp = Pp
module M  = Data.StrMap

let position = let open OpaqueData in declare {
  name = "position";
  doc = "locations in the input file";
  pp = pp_position;
  compare = compare_position;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}

(* types - elpi terms ************************************************** *)

let ty_ctx = State.declare ~name:"toyml:ty_ctx" ~pp:(fun fmt _ -> Format.fprintf fmt "TODO")
  ~init:(fun () -> [])

let tye = let open AlgebraicData in declare {
  ty = Conversion.TyName "tye";
  doc = "Monomorphic type expressions";
  pp = pp_tye;
  constructors = [
    K("(==>)","function space",S(S N),
      B (fun t1 t2 -> Arrow (t1, t2)),
      M (fun ~ok ~ko -> function Arrow(t1,t2) -> ok t1 t2 | _ -> ko ()));
    K("integer","",N,
      B Integer,
      M (fun ~ok ~ko -> function Integer -> ok | _ -> ko ()));
    K("boolean","",N,
      B Boolean,
      M (fun ~ok ~ko -> function Boolean -> ok | _ -> ko ()));
    K("list","",S N,
      B (fun x -> List x),
      M (fun ~ok ~ko -> function List x -> ok x | _ -> ko ()));
    K("pair","",S (S N),
      B (fun x y -> Pair(x,y)),
      M (fun ~ok ~ko -> function Pair (x,y) -> ok x y | _ -> ko ()));
    K("","",A(BuiltInData.string,N),
      BS (fun s st -> st, Var s),
      MS (fun ~ok ~ko -> function
        | Var s -> ok s (fun st -> st, E.mkBound (List.assoc s (State.get ty_ctx st)), [])
        | _ -> ko))
  ]
} |> ContextualConversion.(!<)

let quantification = let open AlgebraicData in declare {
  ty = Conversion.TyName "eq?";
  doc = "kind of quantification";
  pp = pp_quantification;
  constructors = [
    K("eqt","",N,
      B EqualityType,
      M(fun ~ok ~ko -> function EqualityType -> ok | _ -> ko ()));
    K("any","",N,
      B Any,
      M(fun ~ok ~ko -> function Any -> ok | _ -> ko ()));
  ]
} |> ContextualConversion.(!<)

let allc     = E.Constants.declare_global_symbol "all"
let monoc     = E.Constants.declare_global_symbol "mono"

let rec embed_typ : typ Conversion.embedding = fun ~depth st -> function
  | Mono m ->
      let st, tye, gls = tye.Conversion.embed ~depth st m in
      st, E.mkApp monoc tye [], gls
  | All(q,rest) ->
      let st, q, gls = quantification.Conversion.embed ~depth st q in
      x
      ;;


(* terms - elpi terms ************************************************** *)

let appc     = E.Constants.declare_global_symbol "app"
let lamc     = E.Constants.declare_global_symbol "lam"
let letc     = E.Constants.declare_global_symbol "let"
let eqc      = E.Constants.declare_global_symbol "eq"
let literalc = E.Constants.declare_global_symbol "literal"
let globalc  = E.Constants.declare_global_symbol "global"

let nodec    = E.Constants.declare_global_symbol "node"

let rec lookup x = function
  | [] -> E.mkApp globalc (RawOpaqueData.of_string x) []
  | y :: ys when x = y -> E.mkConst (List.length ys)
  | _ :: ys -> lookup x ys

let rec embed st ctx { v; loc } = begin
  match v with
  | Const s -> st, lookup s ctx
  | Int n -> st, E.mkApp literalc (RawOpaqueData.of_int n) []
  | App(h,a) ->
     let st, h = embed st ctx h in
     let st, a = embed st ctx a in
     st, E.mkApp appc h [a]
  | Lam (n,t) ->
     let st, t = embed st (n :: ctx) t in
     st, E.mkApp lamc (E.mkLam t) []
  | Let(n, t, b) ->
     let st, ty = FlexibleData.Elpi.make st t.loc in
     let st, t = embed st ctx t in
     let st, b = embed st (n :: ctx) b in
     st, E.mkApp letc t [ty; E.mkLam b]
  | Eq(lhs, rhs) ->
     let st, lhs = embed st ctx lhs in
     let st, rhs = embed st ctx rhs in
     st, E.mkApp eqc lhs [rhs]
end

let term =
  let open Conversion in
  {
    ty = TyName "term";
    pp_doc = (fun fmt () -> Format.fprintf fmt "The data type of terms")
    pp = Ast.pp_term;
    embed = embed_term;
    readback = readback_term;
  }

(* builtin *************************************************************** *)

exception TypeError of {
  assignments : E.term M.t;
  state : State.t;

  t : E.term;
  ty : E.term;
  ety : E.term;
}
exception NotEqType of {
  assignments : E.term M.t;
  state : State.t;

  t : E.term;
}

let extra_builtins =
 let open BuiltInPredicate in
 let open BuiltInData in
 let open BuiltIn in
 declare ~file_name:"toyml-builtin.elpi" [

  MLCode(Pred("type-error",
    In(any,"the term",
    In(any,"its type",
    In(any,"the type expected by its context",
    Easy("raise a fatal type inference error")))),
    (fun t ty ety ~depth:_ _ { assignments; state } ->
       raise (TypeError{assignments; state; t; ty; ety }))),
  DocNext);

  MLCode(Pred("eqtype-error",
    In(any,"the term",
    Easy("raise a fatal equality type error")),
    (fun t ~depth:_ _ { assignments; state } ->
       raise (NotEqType{assignments; state; t}))),
  DocNext);

]

let _ = BuiltIn.document_file extra_builtins ;;

(* w ********************************************************************* *)

let subtext text fmt ( { Lexing.pos_cnum = a; _ } , { Lexing.pos_cnum = b; _ } ) =
  let open String in
  Format.fprintf fmt "@[<v 2>  %s@;%s@]" text
  (make a ' ' ^ make (b-a) '^' ^ make (length text - b) ' ')

let pp_result text assignments state =
  M.iter (fun k v ->
     let loc = M.find k (State.get rs_output state) in
     Format.printf "@[<v>The term:@ %a@ has type: %a@]@\n@\n"
       (subtext text) loc (Pp.term 0) v)
    assignments

let pp_type_err text t ty ety state =
  let loc = P.find_opt t (State.get rs_positions state) in
  match loc with
  | Some loc ->
      Format.printf "@[<v>Type error:@ %a@ has type %a@ but is expected to have type %a@]@\n%!" (subtext text) loc (Pp.term 0) ty (Pp.term 0) ety
  | None ->
      Format.printf "@[<v>Type error:@ the term: %a@ has type %a@ but is expected to have type %a@]@\n%!" (Pp.term 0) t (Pp.term 0) ty (Pp.term 0) ety

let pp_eqtype_err text t state =
  let loc = P.find_opt t (State.get rs_positions state) in
  match loc with
  | Some loc ->
      Format.printf "@[<v>Equality type constraint unsatisfied at:@ %a@]@\n%!" (subtext text) loc
  | None ->
      Format.printf "@[<v>Equality type constraint unsatisfied at:@ %a@]@\n%!"(Pp.term 0) t

let w =
  (* load the elpi program *)
  let elpi_flags =
    try
      let ic, _ as p = Unix.open_process "elpi -where 2>/dev/null" in
      let w = input_line ic in
      let _ = Unix.close_process p in ["-I";w]
    with _ -> [] in
  let builtins = [Elpi.Builtin.std_builtins; extra_builtins] in
  let elpi, _ = Setup.init ~builtins ~basedir:"./"
    (elpi_flags @ List.tl (Array.to_list Sys.argv)) in

  let p = Parse.program ~elpi ["w.elpi"] in
  let p = Compile.program ~flags:Compile.default_flags ~elpi [p] in

fun (text, ast) ->
  (* run w on a term *)
  let q =
    let open Query in
    let spec = Query { predicate = "main"; arguments = D(term,ast,Q(typ,"Q",N)) } in
    compile p (Ast.Loc.initial "(query)") spec in
  if Array.mem "-typecheck" Sys.argv then begin
    if not (Compile.static_check ~checker:(Elpi.Builtin.default_checker ()) q) then
      failwith "w.elpi does not type check";
  end;

  let exe = Compile.optimize q in

  Format.printf "\n============= W: %s ==============\n%!" text;
  match Execute.once exe with
  | Execute.Success { Data.assignments; state; _ } ->
      pp_result text assignments state
  | Failure -> failwith "w.elpi is buggy"
  | NoMoreSteps -> assert false
  | exception TypeError{assignments; state; t; ty; ety } ->
      pp_result text assignments state;
      pp_type_err text t ty ety state
  | exception NotEqType{assignments; state; t } ->
      pp_result text assignments state;
      pp_eqtype_err text t state
;;

(* main ****************************************************************** *)

let parse s = s, Parser.main Lexer.token (Lexing.from_string s)

let _ =
  try
    while true; do
      w @@ parse @@ input_line stdin;
    done
  with End_of_file -> ()

(* vim:set foldmethod=marker: *)
