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
    | TypeAssignment.Arr (_,_, _, t) when extra > 0 -> aux (extra - 1) t
    | TypeAssignment.UVar r when MutableOnce.is_set r -> aux extra (TypeAssignment.deref r)
    | _ -> false
  in
  aux extra ty

let mk_loc ~loc ?(ty = MutableOnce.make (F.from_string "Spill")) it = { ty; it; loc }

(* TODO store the types in Main *)
let add_spilled (l : spill list) t =
  if l = [] then t
  else
    List.fold_right
      (fun { expr; vars_names } t -> mk_loc ~loc:t.loc @@ App (Scope.mkGlobal ~escape_ns:true (), F.andf, expr, [ t ]))
      l t

let mkApp g c l = if l = [] then Const (g, c) else App (g, c, List.hd l, List.tl l)

let app t args =
  if args = [] then t
  else
    let rec aux { loc; it; ty } : t =
      mk_loc ~loc ~ty
      @@
      match it with
      | App ((Global _ as g), c, x, xs) when F.equal c F.andf -> mkApp g c (aux_last (x :: xs))
      | Impl (b, s, t) -> Impl (b, s, aux t)
      | Const (g, c) -> mkApp g c args
      | App (g, c, x, xs) -> mkApp g c ((x :: xs) @ args)
      | Var _ | Discard | Lam (_, _, _, _) | CData _ | Spill (_, _) | Cast (_, _) -> assert false
    and aux_last = function [] -> assert false | [ x ] -> [ aux x ] | x :: xs -> x :: aux_last xs in
    aux t

(* let args = ref 0  *)

let rec mk_spilled ~loc ctx args n =
  if n = 0 then []
  else
    let f =
      incr args;
      F.from_string (Printf.sprintf "%%arg%d" !args)
    in
    let sp = mk_loc ~loc @@ Var (f, ctx) in
    (f, sp) :: mk_spilled ~loc ctx args (n - 1)

(* barendregt_convention (naive implementation) *)
let rec bc ctx t =
  match t with
  | Lam (None, o, tya, t) -> Lam (None, o, tya, bc_loc ctx t)
  | Lam (Some (c, l), o, tya, t) when List.mem (c, l) ctx ->
      let d = fresh () in
      bc ctx (Lam (Some (d, l), o, tya, rename_loc l c d t))
  | Lam (Some c, o, tya, t) -> Lam (Some c, o, tya, bc_loc (c :: ctx) t)
  | Impl (b, t1, t2) -> Impl (b, bc_loc ctx t1, bc_loc ctx t2)
  | Cast (t, ty) -> Cast (bc_loc ctx t, ty)
  | Spill (t, i) -> Spill (bc_loc ctx t, i)
  | App (g, f, x, xs) -> App (g, f, bc_loc ctx x, List.map (bc_loc ctx) xs)
  | Const _ | Discard | Var _ | CData _ -> t

and bc_loc ctx { loc; ty; it } = { loc; ty; it = bc ctx it }

let rec spill ?(extra = 0) ctx args ({ loc; ty; it } as t) : spills * t list =
  (* Format.eprintf "@[<hov 2>spill %a :@ %a@]\n" pretty t TypeAssignment.pretty (TypeAssignment.deref ty); *)
  match it with
  | CData _ | Discard | Const _ -> ([], [ t ])
  | Cast (t, _) -> spill ctx args t
  | Spill (t, { contents = NoInfo }) -> assert false (* no type checking *)
  | Spill (t, { contents = Phantom _ }) -> assert false (* escapes type checker *)
  | Spill (t, { contents = Main n }) ->
      let vars_names, vars =
        List.split @@ mk_spilled ~loc (List.rev_map (fun (c, l) -> mk_loc ~loc @@ Const (Bound l, c)) ctx) args n
      in
      let spills, t = spill1 ~extra:(List.length vars_names) ctx args t in
      let expr = app t vars in
      (spills @ [ { vars; vars_names; expr } ], vars)
  (* globals and builtins *)
  | App ((Global _ as f), c, { it = Lam (Some v, o, tya, t); loc = tloc; ty = tty }, []) when F.equal F.pif c ->
      let ctx = v :: ctx in
      let spilled, t = spill1 ctx args t in
      ( [],
        [ { loc; ty; it = App (f, c, { it = Lam (Some v, o, tya, add_spilled spilled t); loc = tloc; ty = tty }, []) } ]
      )
  | App ((Global _ as f), c, { it = Lam (Some v, o, tya, t); loc = tloc; ty = tty }, []) when F.equal F.sigmaf c ->
      let ctx = ctx in
      (* not to be put in scope of spills *)
      let spilled, t = spill1 ctx args t in
      ( [],
        [ { loc; ty; it = App (f, c, { it = Lam (Some v, o, tya, add_spilled spilled t); loc = tloc; ty = tty }, []) } ]
      )
  | App (g, c, x, xs) ->
      let last = if F.equal F.andf c then List.length xs else -1 in
      let spills, args =
        List.split @@ List.mapi (fun i -> spill ~extra:(if i = last then extra else 0) ctx args) (x :: xs)
      in
      let args = List.flatten args in
      let spilled = List.flatten spills in
      let it = App (g, c, List.hd args, List.tl args) in
      let extra = extra + List.length args - List.length xs - 1 in
      (* Format.eprintf "%a\nspill %b %d %a : %a\n" Loc.pp loc (is_prop ~extra ty) extra F.pp c TypeAssignment.pretty (TypeAssignment.UVar ty); *)
      if is_prop ~extra ty then ([], [ add_spilled spilled { it; loc; ty } ]) else (spilled, [ { it; loc; ty } ])
  (* TODO: positive/negative postion, for now we assume :- and => are used in the obvious way *)
  | Impl (false, head, premise) ->
      (* head :- premise *)
      let spills_head, head = spill1 ctx args head in
      if spills_head <> [] then error ~loc "Spilling in the head of a clause is not supported";
      let spilled, premise = spill1 ctx args premise in
      let it = Impl (false, head, premise) in
      ([], [ add_spilled spilled { it; loc; ty } ])
  | Impl (true, premise, conclusion) ->
      (* premise => conclusion *)
      let spills_premise, premise = spill1 ctx args premise in
      if spills_premise <> [] then error ~loc "Spilling in the premise of an implication is not supported";
      let spilled, conclusion = spill1 ~extra ctx args conclusion in
      let it = Impl (true, premise, conclusion) in
      ([], [ add_spilled spilled { it; loc; ty } ])
  (* lambda terms *)
  | Lam (None, o, tya, t) ->
      let spills, t = spill1 ctx args t in
      (spills, [ { it = Lam (None, o, tya, t); loc; ty } ])
  | Lam (Some c, o, tya, t) ->
      let spills, t = spill1 (c :: ctx) args t in
      let (t, _), spills =
        map_acc
          (fun (t, n) { vars; vars_names; expr } ->
            let all_names = vars_names @ n in
            ( (t, all_names),
              {
                vars;
                vars_names;
                expr =
                  mk_loc ~loc
                  @@ App (Scope.mkGlobal ~escape_ns:true (), F.pif, mk_loc ~loc @@ Lam (Some c, o, tya, expr), []);
              } ))
          (t, []) spills
      in
      (spills, [ { it = Lam (Some c, o, tya, t); loc; ty } ])
  (* holes *)
  | Var (c, xs) ->
      let spills, args = List.split @@ List.map (spill ctx args) xs in
      let args = List.flatten args in
      let spilled = List.flatten spills in
      let it = Var (c, args) in
      let extra = extra + List.length args - List.length xs in
      if is_prop ~extra ty then ([], [ add_spilled spilled { it; loc; ty } ]) else (spilled, [ { it; loc; ty } ])

and spill1 ?extra ctx args ({ loc } as t) =
  let spills, t = spill ?extra ctx args t in
  let t = if List.length t <> 1 then error ~loc "bad pilling" else List.hd t in
  (spills, t)

let spill ctx t =
  let args = ref 0 in
  (* Format.eprintf "before spill: %a\n" pretty t; *)
  let s, t = spill ctx args t in

  (* Format.eprintf "after spill: %a\n" pretty (List.hd t); *)
  (s, t)

let main t =
  (* if needs_spilling then Format.eprintf "before %a\n" pretty t; *)
  let spills, ts = spill [] (bc_loc [] t) in
  let t =
    match (spills, ts) with
    | [], [ t ] -> t
    | [], _ -> assert false
    | _ :: _, _ -> error ~loc:t.loc "Cannot place spilled expression"
  in
  t
