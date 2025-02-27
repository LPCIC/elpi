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
let ( ++ ) = MutableOnce.create
let ( -- ) = MutableOnce.get
let mk_global name = ScopedTerm.mk_ty_name (Scope.mkGlobal ()) (fs name)
let mk_bound name = ScopedTerm.mk_ty_name (Scope.Bound elpi_language) (fs name)
let mk_local name = ScopedTerm.mk_ty_name elpi_language (fs name)
let build_loc it = ST.{ loc = dummy_loc; ty = MutableOnce.make dummy_str; it }
let app n ag ags = build_loc @@ ST.App (mk_global n, ag, ags)
let lam n bo = build_loc @@ ST.Lam (Some (mk_local n), None, bo)
let const n = build_loc @@ ST.Const (mk_global n)
let local_const n = build_loc @@ ST.Const (mk_bound n)
let var n = build_loc @@ ST.Var (ST.mk_ty_bound_elpi elpi_var @@ fs n, [])
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

let inp = TypeAssignment.MVal Input
let out = TypeAssignment.MVal Output
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

let get_hd_ty ST.{ it } =
  match it with
  | ST.Var (s, _) | App (s, _, _) | Const s ->
      let _, _, s = s in
      s
  | _ -> assert false

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
    |> add_ty "ff" !:(Ty bool) |> add_ty "tt" !:(Ty bool)
    |> (* apply i:T i:P o:R :- if (P T) (R = tt) (R = ff) *)
    add_ty "apply" !:(Lam (fs "A", Ty (uv "A" @->> (uv "A" @->> rprop) @-> bool @-> rprop)))
  in

  let unknown = F.Map.empty in
  let exp = build_ta rprop in
  let is_rule = false in

  let check f test_nb t exp =
    let t = f t in
    let _pp = TA.pp_t_ (MutableOnce.pp TA.pp) in
    if unifyable_ground_ty t exp <> 0 then (
      Format.eprintf "---\nUnexpected result %d: \nactual: @[%a@]\nreference: @[%a@]@." test_nb TA.pretty_mut_once_raw t
        TA.pretty_mut_once_raw exp;
      exit 1)
  in

  let check_type =
    let rec get_uvar = function TA.UVar b -> MutableOnce.get b |> TA.unval |> get_uvar | a -> a in
    let f t = get_uvar @@ TA.unval (MutableOnce.get t.ST.ty) in
    check f
  in

  let check_hd = check (fun t -> TA.UVar (get_hd_ty t)) in

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

    Format.eprintf "The type of the variable X is %a@." TA.pretty_mut_once (TA.UVar (get_hd_ty varX));
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
    check_type 5 ag (rprop @->> rprop);
    check_hd 6 term (rprop @->> (rprop @->> rprop) @-> bool @-> rprop)
  in

  let _ =
    let term = app "apply" (const "tt") [ lam "x" (const "false"); var "R" ] in

    let _ = Type_checker.check ~is_rule:false ~types ~unknown ~exp ~kinds ~type_abbrevs term in
    check_hd 7 term (bool @->> (bool @->> rprop) @-> bool @-> rprop)
  in

  ()
