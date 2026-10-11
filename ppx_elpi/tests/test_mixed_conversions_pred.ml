let file_name = Sys.argv.(1)

open Elpi.API

(* A variant of test_mixed_conversions: the datum with binders has a hand
   written contextual conversion, with a hand written context readback whose
   context is a plain value (a map) and not an object, and the datum converted
   by the ppx has no binders. The predicate is a Pred, not a ContextualPred. *)

let declaration = PPX.empty_declaration ()

(* The datum without binders, converted by the ppx. Having no context, its
   conversion works in any context *)

type color = Red | Green | Blue of int
[@@deriving show, elpi { declaration }]

let color :
    'c 'csts.
    (color, 'c, 'csts) ContextualConversion.t = color

(* The datum with binders, with a hand written conversion. The names of the
   variables are in the context, a map from the constants (the bound variables
   of the program) to strings, built by reading back the hypotheses
   [known x "name"]. A binder extends the context. *)

type lam = V of string | Ap of lam * lam | Lm of string * lam
[@@deriving show]

type context = string RawData.Constants.Map.t

let c_ap = RawData.Constants.declare_global_symbol "ap"
let c_lm = RawData.Constants.declare_global_symbol "lm"
let c_known = RawData.Constants.declare_global_symbol "known"

(* The context readback: it looks for the hypotheses [known x "name"] *)
let known_ctx :
    (context, Data.constraints) ContextualConversion.ctx_readback =
  fun ~depth hyps csts state ->
    let ctx, state, gls =
      List.fold_left (fun (ctx, state, gls) { RawData.hdepth; hsrc } ->
        match RawData.look ~depth:hdepth hsrc with
        | RawData.App(c,x,[s]) when c = c_known ->
            begin match RawData.look ~depth:hdepth x with
            | RawData.Const l ->
                let state, s, g = BuiltInData.string.readback ~depth:hdepth state s in
                RawData.Constants.Map.add l s ctx, state, g @ gls
            | _ -> ctx, state, gls
            end
        | _ -> ctx, state, gls)
        (RawData.Constants.Map.empty, state, []) (RawData.of_hyps hyps) in
    state, ctx, csts, gls

let level_of (ctx : context) name =
  match RawData.Constants.Map.fold
          (fun l n acc -> if n = name then Some l else acc) ctx None with
  | Some l -> l
  | None -> Utils.type_error ("unbound variable " ^ name)

let rec embed_lam ~depth (ctx : context) csts state = function
  | V s -> state, RawData.mkBound (level_of ctx s), []
  | Ap(a,b) ->
      let state, a, ga = embed_lam ~depth ctx csts state a in
      let state, b, gb = embed_lam ~depth ctx csts state b in
      state, RawData.mkAppGlobal c_ap a [b], ga @ gb
  | Lm(name,t) ->
      let state, s, gs = BuiltInData.string.embed ~depth state name in
      let ctx = RawData.Constants.Map.add depth name ctx in
      let state, t, g = embed_lam ~depth:(depth+1) ctx csts state t in
      state, RawData.mkAppGlobal c_lm s [RawData.mkLam t], gs @ g

let rec readback_lam ~depth (ctx : context) csts state t =
  match RawData.look ~depth t with
  | RawData.Const l ->
      begin match RawData.Constants.Map.find_opt l ctx with
      | Some s -> state, V s, []
      | None -> Utils.type_error "unbound variable"
      end
  | RawData.App(c,a,[b]) when c = c_ap ->
      let state, a, ga = readback_lam ~depth ctx csts state a in
      let state, b, gb = readback_lam ~depth ctx csts state b in
      state, Ap(a,b), ga @ gb
  | RawData.App(c,s,[f]) when c = c_lm ->
      let state, s, gs = BuiltInData.string.readback ~depth state s in
      begin match RawData.look ~depth f with
      | RawData.Lam body ->
          let ctx = RawData.Constants.Map.add depth s ctx in
          let state, t, g = readback_lam ~depth:(depth+1) ctx csts state body in
          state, Lm(s,t), gs @ g
      | _ -> Utils.type_error "lm expects a lambda"
      end
  | _ -> Utils.type_error "not a lam"

let lam : (lam, context, Data.constraints) ContextualConversion.t = {
  ty = TyName "lam";
  pp = pp_lam;
  pp_doc = (fun fmt () ->
    Format.fprintf fmt "data lam.@\n";
    Format.fprintf fmt "builtin symb ap : lam -> lam -> lam = \"0\".@\n";
    Format.fprintf fmt "builtin symb lm : string -> (lam -> lam) -> lam = \"0\".@\n@\n");
  embed = embed_lam;
  readback = readback_lam;
}

(* The predicate, a Pred, with the context readback above *)

open BuiltInPredicate.Notation

let describe = BuiltInPredicate.Pred("describe",
  CIn(lam,"T",
  CIn(color,"C",
  Out(BuiltInData.string,"S",
  COut(lam,"R",
  Read(known_ctx,"describes a term and a colour, and applies the term to y"))))),
  fun (t : lam) (c : color) (_s : string BuiltInPredicate.oarg)
    (_r : lam BuiltInPredicate.oarg)
    ~depth:_ (ctx : context) (_cst : Data.constraints) (_state : State.t) ->
    !: (Format.asprintf "%a ; %a ; known: %s"
         pp_color c pp_lam t
         (String.concat ", " (List.map snd (RawData.Constants.Map.bindings ctx))))
    +! Ap(t, V "y"))

let builtin = let open BuiltIn in
  BuiltIn.declare ~file_name ((PPX.to_list declaration) @ [
    MLDataC lam;
    (* the hypotheses read by the context readback *)
    LPCode "builtin func known lam -> string.";
    MLCode(describe,DocAbove);
  ])

let program = {|
main :-
  pi a b\
    known a "x" ==> known b "y" ==>
      sigma S R\
        describe (lm "z" z\ ap z (ap a b)) (blue 3) S R,
        print S,
        % the name y is mapped back to the constant b by the context
        print R.
|}

let () = Ppx_tests_lib.run_program builtin program
