open Elpi_parser
open Ast
open Elpi_compiler
open Compiler_data
module F = Func
module ST = ScopedTerm
module TA = TypeAssignment

let fs = F.from_string
let dummy_loc = Loc.initial ""
let dummy_str = F.dummyname
let build_loc it = ST.{ loc = dummy_loc; ty = MutableOnce.make dummy_str; it }
let build_scope () = Scope.Global { escape_ns = true; decl_id = Scope.dummy_type_decl_id }
let app n ag ags = build_loc @@ ST.App (build_scope (), fs n, ag, ags)
let lam n bo = build_loc @@ ST.Lam (Some (fs n, elpi_language), None, MutableOnce.make dummy_str, bo)
let const n = build_loc @@ ST.Const (build_scope (), fs n)
let local_const n = build_loc @@ ST.Const (Scope.Bound elpi_language, fs n)
let var n = build_loc @@ ST.Var (fs n, [])
let build_ta a = TA.Val a
let rprop = TA.Prop Relation
let bool = TA.Cons (fs "bool")

(** builds type_skema_with_id  *)
let ( !: ) =
  let id = ref 0 in
  fun ag ->
    incr id;
    let id = IdPos.make_str (string_of_int !id) in
    TA.Single (id, (ag : TA.skema))

let inp = TypeAssignment.MVal Mode.Input
let out = TypeAssignment.MVal Mode.Output
let ( @->> ) a1 a2 = TA.Arr (inp, NotVariadic, a1, a2)
let ( @-> ) a1 a2 = TA.Arr (out, NotVariadic, a1, a2)
let uv n = TA.UVar (fs n)

let rec deref_term = function
  | TA.UVar t1 -> (
      let t = TA.deref t1 in
      match t with UVar _ -> t | t -> deref_term t)
  | (Any | Prop _ | Cons _) as t -> t
  | App (a, b, c) -> App (a, deref_term b, List.map deref_term c)
  | Arr (m, v, l, r) -> Arr (TA.deref_tmode m, v, deref_term l, deref_term r)

let unifyable_ground_ty (t1 : TA.t MutableOnce.t TA.t_) (t2 : TA.t MutableOnce.t TA.t_) =
  TA.compare_t__
    (fun a b -> assert false) (* Not UVar left *)
    (fun a b -> match (a, b) with TA.MVal a, MVal b -> Mode.compare a b | _, _ -> assert false)
    (deref_term t1) (deref_term t2)

let _ =
  Elpi_util.Util.set_warn (fun ?loc _ -> ());

  let type_abbrevs = F.Map.empty in
  let kinds = F.Map.empty in
  let types : Type_checker.env = F.Map.empty in
  let add_ty k v ty = F.Map.add (fs k) v ty in
  let types =
    add_ty "false" !:(Ty rprop) types
    |> add_ty "f" !:(Ty (rprop @->> rprop @-> rprop))
    |> add_ty "=" !:(Lam (fs "A", Ty (uv "A" @->> uv "A" @->> rprop)))
    |> (* apply i:T i:P o:R :- if (P T) (R = tt) (R = ff) *)
    add_ty "apply" !:(Lam (fs "A", Ty (uv "A" @->> (uv "A" @->> rprop) @-> bool @-> rprop)))
  in

  let unknown = F.Map.empty in
  let exp = build_ta rprop in
  let is_rule = false in

  let check_type test_nb t exp =
    let rec get_uvar = function TA.UVar b -> MutableOnce.get b |> TA.unval |> get_uvar | a -> a in
    let t = get_uvar @@ TA.unval (MutableOnce.get t.ST.ty) in
    let _pp = TA.pp_t_ (MutableOnce.pp TA.pp) in
    if unifyable_ground_ty t exp <> 0 then (
      Format.eprintf "---\nUnexpected result %d: \nactual: @[%a@]\nreference: @[%a@]@." test_nb TA.pretty_mut_once_raw t
        TA.pretty_mut_once_raw exp;
      exit 1)
  in

  let _ =
    let varX = var "X" in
    let varY = var "Y" in
    let term = app "=" (app "f" varY []) [ varX ] in

    let _ = Type_checker.check ~is_rule ~types ~unknown ~exp ~kinds ~type_abbrevs term in
    check_type 1 varX (rprop @-> rprop)
  in

  let _ =
    let varX = var "X" in
    let term = app "=" (const "f") [ varX ] in
    let _ = Type_checker.check ~is_rule ~types ~unknown ~exp ~kinds ~type_abbrevs term in
    check_type 2 varX (rprop @->> rprop @-> rprop)
  in

  let _ =
    let varX = var "X" in
    let term = app "=" (lam "x" (app "f" (local_const "x") [])) [ varX ] in

    let _ = Type_checker.check ~is_rule ~types ~unknown ~exp ~kinds ~type_abbrevs term in
    check_type 3 varX (rprop @->> rprop @-> rprop)
  in

  let _ =
    let varX = var "X" in
    let term = app "=" (lam "x" @@ lam "y" (app "f" (local_const "x") [ local_const "y" ])) [ varX ] in

    let _ = Type_checker.check ~is_rule ~types ~unknown ~exp ~kinds ~type_abbrevs term in
    (* Format.eprintf "The inferred type is %a@." TA.pretty_mut_once_raw (UVar varX.ty); *)
    check_type 4 varX (rprop @->> rprop @-> rprop)
  in

  let _ =
    let ag = lam "x" (app "f" (local_const "x") [ var "A" ]) in

    let term = app "apply" (const "false") [ ag; var "R" ] in

    let _ = Type_checker.check ~is_rule:false ~types ~unknown ~exp ~kinds ~type_abbrevs term in
    (* Format.eprintf "The inferred type is %a@." TA.pretty_mut_once_raw (UVar varX.ty); *)
    check_type 5 ag (rprop @->> rprop)
  in

  ()
