(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Elpi_util.Util
open Compiler_data
module C = Constants
open ScopedTerm

type spill = { vars : t list; vars_names : F.t list; expr : t }
type spills = spill list

let is_prop ~extra x =
  let ty = TypeAssignment.deref x in
  let rec aux extra = function
    | TypeAssignment.Prop _ -> true
    (* | TypeAssignment.(App(f,Prop _,[])) when F.show f = "list" -> true hack since the type checker unifies prop with list prop *)
    | TypeAssignment.Arr (_, _, _, t) when extra > 0 -> aux (extra - 1) t
    | TypeAssignment.UVar r when MutableOnce.is_set r -> aux extra (TypeAssignment.deref r)
    | _ -> false
  in
  aux extra ty

let mk_global ~types f l =
  (* TODO: check only builtins *)
  let s = Symbol.make_builtin f in
  let f_ty = TypingEnv.(resolve_symbol s types).ty |> (fun x -> TypeAssignment.apply x l) |> TypeAssignment.create in
  (Scope.mkResolvedGlobal types s), f, f_ty

let pif_ty_name ~types (_,_,ty) : 'a ty_name = mk_global ~types F.pif [TypeAssignment.deref ty]
let pif_ty ~types ty = let _,_,ty = pif_ty_name ~types ty in ty
let pif_arg_ty ~types ty =
  match TypeAssignment.deref @@ pif_ty ~types ty with
  | TypeAssignment.Arr(_,_,x,_) -> TypeAssignment.create x
  | _ -> assert false

let mk_loc ~loc ~ty it = { ty; it; loc }

(* TODO store the types in Main *)
let add_spilled ~types (l : spill list) t =
  if l = [] then t
  else
    List.fold_right
      (fun { expr; vars_names } t ->
        mk_loc ~loc:t.loc ~ty:TypeAssignment.(create (Prop Elpi_parser.Ast.Structured.Function))
        @@ App (mk_global ~types F.andf [], expr, [ t ]))
      l t

let mkApp n l = if l = [] then Const n else App (n, List.hd l, List.tl l)

let is_symbol ~types b = function
| Scope.Global { resolved_to = x } ->
  begin match SymbolResolver.resolved_to types x with
  | Some s  -> TypingEnv.same_symbol types s b
  | _ -> anomaly "unresolved global symbol"
  end
| _ -> false

let app ~types t args =
  if args = [] then t
  else
    let rec aux { loc; it; ty } : t =
      mk_loc ~loc ~ty
      @@
      match it with
      | App (((s, _, _) as n), x, xs) when is_symbol ~types Elpi_runtime.Data.Global_symbols.and_ s -> mkApp n (aux_last (x :: xs))
      | Impl (b, s, t) -> Impl (b, s, aux t)
      | Const n -> mkApp n args
      | App (n, x, xs) -> mkApp n ((x :: xs) @ args)
      | Var (c,l) -> Var (c,l @ args)
      | Discard | Lam (_, _, _) | CData _ | Spill (_, _) | Cast (_, _) -> assert false
    and aux_last = function [] -> assert false | [ x ] -> [ aux x ] | x :: xs -> x :: aux_last xs in
    aux t

let mk_spilled ~loc ~ty ctx args n : (F.t * t) list =
  (* builds the type of the spilled variables, all variables has same type *)
  let builf_head_ty tgt_ty =
    let rec aux = function
      | [] -> tgt_ty
      | ScopedTerm.{ ty } :: tl ->
          TypeAssignment.(Arr (MRef (MutableOnce.make F.dummyname), NotVariadic, deref ty, aux tl))
    in
    TypeAssignment.create (aux ctx)
  in
  let rec aux n ty =
    let f =
      incr args;
      F.from_string (Printf.sprintf "%%arg%d" !args)
    in
    let built_tm ty =
      let hd_ty = builf_head_ty ty in
      mk_loc ~loc ~ty:(TypeAssignment.create ty) @@ Var ((Bound elpi_var, f, hd_ty), ctx)
    in
    if n = 0 then []
    else
      match ty with
      | TypeAssignment.Arr (_, _, l, r) -> (f, built_tm l) :: aux (n-1) r
      | UVar r when MutableOnce.is_set r -> aux n (TypeAssignment.deref r)
      | _ -> anomaly "type abbreviations and spilling, not implemented"
  in
  aux n ty

(* barendregt_convention (naive implementation) *)
let rec bc ctx t =
  match t with
  | Lam (None, o, t) -> Lam (None, o, bc_loc ctx t)
  | Lam (Some (l, c, tya), o, t) when List.mem (c, l) ctx ->
      let d = fresh () in
      bc ctx (Lam (Some (l, d, tya), o, rename_loc l c d t))
  | Lam ((Some (l, c, _) as abs), o, t) -> Lam (abs, o, bc_loc ((c, l) :: ctx) t)
  | Impl (b, t1, t2) -> Impl (b, bc_loc ctx t1, bc_loc ctx t2)
  | Cast (t, ty) -> Cast (bc_loc ctx t, ty)
  | Spill (t, i) -> Spill (bc_loc ctx t, i)
  | App (hd, x, xs) -> App (hd, bc_loc ctx x, List.map (bc_loc ctx) xs)
  | Const _ | Discard | Var _ | CData _ -> t

and bc_loc ctx { loc; ty; it } = { loc; ty; it = bc ctx it }

let rec spill ~types ?(extra = 0) (ctx : string ty_name list) args ({ loc; ty; it } as t) : spills * t list =
  (* Format.eprintf "@[<hov 2>spill %a :@ %a@]\n" pretty t TypeAssignment.pretty (TypeAssignment.deref ty); *)
  match it with
  | CData _ | Discard | Const _ -> ([], [ t ])
  | Cast (t, _) -> spill ~types ctx args t
  | Spill (t, { contents = NoInfo }) -> assert false (* no type checking *)
  | Spill (t, { contents = Phantom _ }) -> assert false (* escapes type checker *)
  | Spill (t, { contents = Main n }) ->
      let ty = t.ty in
      (* Format.eprintf "Spilling of %a with ty %a requires %d slots@." ScopedTerm.pretty_ it TypeAssignment.pretty_mut_once (UVar ty) n; *)
      let vars_names, vars =
        List.split
        @@ mk_spilled ~loc ~ty:(TypeAssignment.deref ty)
             (List.rev_map (fun (l, c, ty) -> mk_loc ~loc ~ty @@ Const (Bound l, c, ty)) ctx)
             args n
      in
      let spills, t = spill1 ~types ~extra:(List.length vars_names) ctx args t in
      let expr = app ~types t vars in
      (* Format.eprintf "Spilled %a@." ScopedTerm.pretty expr; *)
      (spills @ [ { vars; vars_names; expr } ], vars)
  (* globals and builtins *)
  | App (((s, _, _) as hd), { it = Lam (Some v, o, t); loc = tloc; ty = tty }, []) when is_symbol ~types Elpi_runtime.Data.Global_symbols.pi s ->
      let ctx = v :: ctx in
      let spilled, t = spill1 ~types ctx args t in
      ([], [ { loc; ty; it = App (hd, { it = Lam (Some v, o, add_spilled ~types spilled t); loc = tloc; ty = tty }, []) } ])
  | App (((s, _, _) as hd), { it = Lam (Some v, o, t); loc = tloc; ty = tty }, []) when is_symbol ~types Elpi_runtime.Data.Global_symbols.sigma s ->
      let ctx = ctx in
      (* not to be put in scope of spills *)
      let spilled, t = spill1 ~types ctx args t in
      ([], [ { loc; ty; it = App (hd, { it = Lam (Some v, o, add_spilled ~types spilled t); loc = tloc; ty = tty }, []) } ])
  | App (((s,_,_) as hd), x, xs) ->
      let last = if is_symbol ~types Elpi_runtime.Data.Global_symbols.and_ s then List.length xs else -1 in
      let spills, args =
        List.split @@ List.mapi (fun i -> spill ~types ~extra:(if i = last then extra else 0) ctx args) (x :: xs)
      in
      let args = List.flatten args in
      let spilled = List.flatten spills in
      let it = App (hd, List.hd args, List.tl args) in
      let extra = extra + List.length args - List.length xs - 1 in
      (* Format.eprintf "%a\nspill %b %d %a : %a\n" Loc.pp loc (is_prop ~extra ty) extra F.pp c TypeAssignment.pretty (TypeAssignment.UVar ty); *)
      if is_prop ~extra ty then ([], [ add_spilled ~types spilled { it; loc; ty } ]) else (spilled, [ { it; loc; ty } ])
  (* TODO: positive/negative postion, for now we assume :- and => are used in the obvious way *)
  | Impl (R2L, head, premise) ->
      (* head :- premise *)
      let spills_head, head = spill1 ~types ctx args head in
      if spills_head <> [] then error ~loc "Spilling in the head of a clause is not supported";
      let spilled, premise = spill1 ~types ctx args premise in
      let it = Impl (R2L, head, premise) in
      ([], [ add_spilled ~types spilled { it; loc; ty } ])
  | Impl ((L2R|L2RBang) as kind, premise, conclusion) ->
      (* premise => conclusion *)
      let spills_premise, premise = spill1 ~types ctx args premise in
      if spills_premise <> [] then error ~loc "Spilling in the premise of an implication is not supported";
      let spilled, conclusion = spill1 ~types ~extra ctx args conclusion in
      let it = Impl (kind, premise, conclusion) in
      ([], [ add_spilled ~types spilled { it; loc; ty } ])
  (* lambda terms *)
  | Lam (None, o, t) ->
      let spills, t = spill1 ~types ctx args t in
      (spills, [ { it = Lam (None, o, t); loc; ty } ])
  | Lam ((Some c as abs), o, t) ->
      let spills, t = spill1 ~types (c :: ctx) args t in
      let (t, _), spills =
        map_acc
          (fun (t, n) { vars; vars_names; expr } ->
            let all_names = vars_names @ n in
            ( (t, all_names),
              {
                vars;
                vars_names;
                expr =
                  mk_loc ~loc ~ty:(pif_ty ~types  c) @@ App (pif_ty_name ~types c, mk_loc ~loc ~ty:(pif_arg_ty ~types c) @@ Lam (abs, o, expr), []);
              } ))
          (t, []) spills
      in
      (spills, [ { it = Lam (abs, o, t); loc; ty } ])
  (* holes *)
  | Var (c, xs) ->
      let spills, args = List.split @@ List.map (spill ~types ctx args) xs in
      let args = List.flatten args in
      let spilled = List.flatten spills in
      let it = Var (c, args) in
      let extra = extra + List.length args - List.length xs in
      if is_prop ~extra ty then ([], [ add_spilled ~types spilled { it; loc; ty } ]) else (spilled, [ { it; loc; ty } ])

and spill1 ~types ?extra ctx args ({ loc } as t) =
  let spills, t = spill ~types ?extra ctx args t in
  let t = if List.length t <> 1 then error ~loc "bad pilling" else List.hd t in
  (spills, t)

let spill ~types ctx t =
  let args = ref 0 in
  (* Format.eprintf "before spill: %a\n" pretty t; *)
  let s, t = spill ~types ctx args t in

  (* Format.eprintf "after spill: %a\n" pretty (List.hd t); *)
  (s, t)

let main ~types t =
  (* if needs_spilling then Format.eprintf "before %a\n" pretty t; *)
  let spills, ts = spill ~types [] (bc_loc [] t) in
  let t =
    match (spills, ts) with
    | [], [ t ] -> t
    | [], _ -> assert false
    | _ :: _, _ -> error ~loc:t.loc "Cannot place spilled expression"
  in
  t
