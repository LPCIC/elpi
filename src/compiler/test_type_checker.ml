open Elpi_parser
open Ast
open Elpi_compiler
open Compiler_data
module F = Func
module ST = ScopedTerm
module TA = TypeAssignment

let fs = F.from_string
let dummy_loc = Loc.initial ""
let dummy_str = F.from_string ""
let build_loc it = ST.{ loc = dummy_loc; ty = MutableOnce.make dummy_str; it }
let build_scope () = Scope.Global { escape_ns = true; decl_id = Scope.dummy_type_decl_id }
let app n ag ags = build_loc @@ ST.App (build_scope (), fs n, ag, ags)
let const n = build_loc @@ ST.Const (build_scope (), fs n)
let var n = build_loc @@ ST.Var (fs n, [])
let build_ta a = TA.Val a
let rprop = TA.Prop Relation

(** builds type_skema_with_id  *)
let ( !: ) =
  let id = ref 0 in
  fun ag ->
    incr id;
    let id = IdPos.make_str (string_of_int !id) in
    TA.Single (id, (ag : TA.skema))

let ( -->> ) a1 a2 = TA.Arr (Input, NotVariadic, a1, a2)
let ( --> ) a1 a2 = TA.Arr (Output, NotVariadic, a1, a2)
let uv n = TA.UVar (fs n)

let _ =
  Elpi_util.Util.set_warn (fun ?loc _ -> ());

  let type_abbrevs = F.Map.empty in
  let kinds = F.Map.empty in
  let types : Type_checker.env = F.Map.empty in
  let add_ty ty k v = F.Map.add (fs k) v ty in
  let types = add_ty types "f" !:(Ty (rprop -->> (rprop -->> rprop))) in
  let types = add_ty types "=" !:(Lam (fs "A", Ty (uv "A" -->> (uv "A" -->> rprop)))) in

  let unknown = F.Map.empty in
  let exp = build_ta rprop in
  let is_rule = false in

  let check_type t exp =
    let rec get_uvar = function TA.UVar b -> MutableOnce.get b |> TA.unval |> get_uvar | a -> a in
    let t = get_uvar @@ TA.unval (MutableOnce.get t.ST.ty) in
    (* let pp = TA.pp_t_ (MutableOnce.pp TA.pp) in *)
    if t <> exp then (
      Format.eprintf "Unexpected result: \nactual: @[%a@]\nreference: @[%a@]\n" TA.pretty_mut_once t TA.pretty_mut_once exp;
      exit 1)
  in

  let _ =
    let varX = var "X" in
    let varY = var "Y" in
    let term = app "=" (app "f" varY []) [ varX ] in

    let _ = Type_checker.check ~is_rule ~types ~unknown ~exp ~kinds ~type_abbrevs term in
    check_type varX (rprop --> rprop) (*TODO: should be rprop -->> rprop*)
  in

  let _ =
    let varX = var "X" in
    let term = app "=" (const "f") [ varX ] in
    let _ = Type_checker.check ~is_rule ~types ~unknown ~exp ~kinds ~type_abbrevs term in
    check_type varX (rprop -->> (rprop -->> rprop))
  in

  ()
