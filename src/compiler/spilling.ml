(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Elpi_util.Util
open Compiler_data
module C = Constants
open ScopedTerm

type spill = { vars_names : string ty_name list; expr : t }
type spills = spill list

let args_missing_to_prop x =
  let ty = TypeAssignment.deref x in
  let rec aux extra = function
    | TypeAssignment.Prop _ -> Some (List.rev extra)
    (* | TypeAssignment.(App(f,Prop _,[])) when F.show f = "list" -> true hack since the type checker unifies prop with list prop *)
    | TypeAssignment.Arr (_,Elpi_parser.Ast.Structured.NotVariadic, ty, t) as arrow -> aux ((TypeAssignment.create ty,TypeAssignment.create arrow) :: extra) t
    | TypeAssignment.Arr (_,Elpi_parser.Ast.Structured.Variadic, _, t) -> aux extra t
    | TypeAssignment.UVar r when MutableOnce.is_set r -> aux extra (TypeAssignment.deref r)
    | _ -> None
  in
  aux [] ty

let is_prop ~extra x =
  match args_missing_to_prop x with
  | Some n -> List.length n = extra
  | None -> false

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
        vars_names
        (* Format.eprintf "fold %a\n" ScopedTerm.pretty t; *)
         |> List.fold_left (fun t (_,_,vty as v) ->
            mk_loc ~loc:t.loc ~ty:t.ty
            @@ App (mk_global ~types F.sigmaf [TypeAssignment.deref vty],
              mk_loc ~loc:t.loc ~ty:TypeAssignment.(create (Arr (MRef (MutableOnce.make F.dummyname), NotVariadic,deref vty,deref t.ty)))
              @@ Lam(Some v,None,t)
              ,[])
          )
        (mk_loc ~loc:t.loc ~ty:TypeAssignment.(create (Prop Elpi_parser.Ast.Structured.Function))
        @@ App (mk_global ~types F.andf [], expr, [ t ])))
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
      (* | App (((s, _, _) as n), { it = Lam(m,o,t); loc; ty } , []) when is_symbol ~types Elpi_runtime.Data.Global_symbols.sigma s -> mkApp n [{ it = Lam(m,o,aux t); loc; ty }] *)
      | Impl (b, s, t) -> Impl (b, s, aux t)
      | Const n -> mkApp n args
      | App (n, x, xs) -> mkApp n ((x :: xs) @ args)
      | Var (c,l) -> Var (c,l @ args)
      | Discard | Lam (_, _, _) | CData _ | Spill (_, _) | Cast (_, _) -> assert false
    and aux_last = function [] -> assert false | [ x ] -> [ aux x ] | x :: xs -> x :: aux_last xs in
    aux t

let mk_spilled ~loc ~ty args n : (string ty_name * t) list =
  (* builds the type of the spilled variables, all variables has same type *)
  (* let builf_head_ty tgt_ty =
    let rec aux = function
      | [] -> tgt_ty
      | ScopedTerm.{ ty } :: tl ->
          TypeAssignment.(Arr (MRef (MutableOnce.make F.dummyname), NotVariadic, deref ty, aux tl))
    in
    TypeAssignment.create (aux ctx)
  in *)
  let rec aux n ty =
    if n = 0 then []
    else
    let f =
      incr args;
      F.from_string (Printf.sprintf "%%spill%d" !args)
    in
    let built_tm ty =
      let hd_ty = TypeAssignment.create ty in
      mk_loc ~loc ~ty:hd_ty @@ Const (Bound elpi_language, f, hd_ty)
    in
      match ty with
      | TypeAssignment.Arr (_, _, l, r) -> ((elpi_language,f,TypeAssignment.create l), built_tm l) :: aux (n-1) r
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

let not_from_pi (_,b) = b = false
let from_pi (_,b) = b = true

let rec apply what v = function
  | App ((Bound l, f, hd_ty), x, xs) when l = elpi_language && List.exists (fun (_,f',_) -> F.equal f f') what ->
      App ((Bound l, f, TypeAssignment.(create @@ Arr (MRef (MutableOnce.make F.dummyname), NotVariadic, deref v.ty,deref hd_ty))), v, x :: xs)
  | Const (Bound l, f, hd_ty) when l = elpi_language && List.exists (fun (_,f',_) -> F.equal f f') what ->
      App ((Bound l, f, TypeAssignment.(create @@ Arr (MRef (MutableOnce.make F.dummyname), NotVariadic, deref v.ty,deref hd_ty))), v, [])
  | App(f,x,xs) -> App(f,apply_loc what v x,smart_map (apply_loc what v) xs)
  | Lam(n,o,t) -> Lam(n,o,apply_loc what v t)
  | Impl(d,t1,t2) -> Impl(d,apply_loc what v t1,apply_loc what v t2)
  | Cast(t,e) -> Cast(apply_loc what v t,e)
  | Spill _ -> assert false
  | CData _ | Discard | Const _ | Var _ as x -> x
and apply_loc what v { loc; ty; it } = { loc; ty; it = apply what v it }

let apply_loc what v t =
  (* Format.eprintf "apply %a to %a in %a\n" (pplist (fun fmt (s,_,_) -> Format.fprintf fmt "%s" s) " ") what ScopedTerm.pretty v ScopedTerm.pretty t; *)
  let t = apply_loc what v t in
  (* Format.eprintf "apply=%a\n" ScopedTerm.pretty t; *)
  t

let rec spill ~types ?(extra = 0) args ({ loc; ty; it } as t) : spills * t list =
  (* Format.eprintf "@[<hov 2>spill %a :@ %a@]\n" pretty t TypeAssignment.pretty (TypeAssignment.deref ty); *)
  match it with
  | CData _ | Discard | Const _ -> ([], [ t ])
  | Cast (t, _) -> spill ~types args t
  | Spill (t, { contents = NoInfo }) -> assert false (* no type checking *)
  | Spill (t, { contents = Phantom _ }) -> assert false (* escapes type checker *)
  | Spill (t, { contents = Main n }) ->
      let ty = t.ty in
      (* Format.eprintf "Spilling of %a with ty %a requires %d slots@." ScopedTerm.pretty_ it TypeAssignment.pretty_mut_once (UVar ty) n; *)
      let vars_names, vars =
        List.split
        @@ mk_spilled ~loc ~ty:(TypeAssignment.deref ty)
             args n
      in
      let t = app ~types t vars in
      let spills, t = spill1 ~types ~extra:(List.length vars_names) args t in
      (* Format.eprintf "Spilled %a@." ScopedTerm.pretty t; *)
      (spills @ [ { vars_names; expr = t } ], vars)
  (* globals and builtins *)
  | App (((s, _, _) as hd), { it = Lam (Some v, o, t); loc = tloc; ty = tty }, []) when is_symbol ~types Elpi_runtime.Data.Global_symbols.pi s ->
      let spilled, t = spill1 ~types args t in
      ([], [ { loc; ty; it = App (hd, { it = Lam (Some v, o, add_spilled ~types spilled t); loc = tloc; ty = tty }, []) } ])
  | App (((s, _, _) as hd), { it = Lam (Some v, o, t); loc = tloc; ty = tty }, []) when is_symbol ~types Elpi_runtime.Data.Global_symbols.sigma s ->
      (* not to be put in scope of spills *)
      let spilled, t = spill1 ~types args t in
      ([], [ { loc; ty; it = App (hd, { it = Lam (Some v, o, add_spilled ~types spilled t); loc = tloc; ty = tty }, []) } ])
  | App (((s,_,_) as hd), x, xs) ->
      let mk_eta_var () = incr args; F.from_string @@ Format.asprintf "%%eta%d" !args in
      let last = if is_symbol ~types Elpi_runtime.Data.Global_symbols.and_ s then List.length xs else -1 in
      let spills, args =
        List.split @@ List.mapi (fun i -> spill ~types ~extra:(if i = last then extra else 0) args) (x :: xs)
      in
      let args = List.flatten args in
      let spilled = List.flatten spills in
      let it = App (hd, List.hd args, List.tl args) in
      let extra = extra + List.length args - List.length xs - 1 in
      (* Format.eprintf "%a\nspill %b %d %a : %a\n" Loc.pp loc (is_prop ~extra ty) extra F.pp c TypeAssignment.pretty (TypeAssignment.UVar ty); *)
      if is_prop ~extra ty then ([], [ add_spilled ~types spilled { it; loc; ty } ])
      else
        begin match args_missing_to_prop ty with
        | None -> (spilled, [ { it; loc; ty } ])
        | Some missing ->
            let rec mk_lam l t =
              match l with
              | [] -> t
              | (v,ty) :: vs -> {loc;ty;it = Lam(Some v,None,mk_lam vs t)} in
            let missing_vars = List.map (fun (ty,arrow) -> 
                let v = mk_eta_var () in
                ((elpi_language, v, ty), arrow)) missing in
            let missing_args = List.map (fun ((l,v,t),_) -> { ty; loc; it = Const(Bound l,v,t) }) missing_vars in
            ([], [ mk_lam missing_vars @@ add_spilled ~types spilled (app ~types { it; loc; ty } missing_args) ])
        end
  (* TODO: positive/negative postion, for now we assume :- and => are used in the obvious way *)
  | Impl (R2L, head, premise) ->
      (* head :- premise *)
      let spills_head, head = spill1 ~types args head in
      if spills_head <> [] then error ~loc "Spilling in the head of a clause is not supported";
      let spilled, premise = spill1 ~types args premise in
      let it = Impl (R2L, head, premise) in
      ([], [ add_spilled ~types spilled { it; loc; ty } ])
  | Impl ((L2R|L2RBang) as kind, premise, conclusion) ->
      (* premise => conclusion *)
      let spills_premise, premise = spill1 ~types args premise in
      if spills_premise <> [] then error ~loc "Spilling in the premise of an implication is not supported";
      let spilled, conclusion = spill1 ~types ~extra args conclusion in
      let it = Impl (kind, premise, conclusion) in
      ([], [ add_spilled ~types spilled { it; loc; ty } ])
  (* lambda terms *)
  | Lam (None, o, t) ->
      let spills, t = spill1 ~types args t in
      (spills, [ { it = Lam (None, o, t); loc; ty } ])
  | Lam ((Some c as abs), o, t) ->
      let spills, t = spill1 ~types args t in
      let t, spills =
        let s,f,ty = c in
        map_acc
          (fun t { vars_names; expr } ->
            let bc = mk_loc ~loc ~ty (Const(Bound elpi_language,f,ty)) in
            ( apply_loc vars_names bc t,
              {
                vars_names = List.map (fun (x,y,vty) ->
                   x,y,TypeAssignment.(create @@ Arr (MRef (MutableOnce.make F.dummyname), NotVariadic, deref ty,deref vty))) vars_names;
                expr =
                  mk_loc ~loc ~ty:(pif_ty ~types  c) @@ App (pif_ty_name ~types c, mk_loc ~loc ~ty:(pif_arg_ty ~types c) @@ Lam (abs, o, apply_loc vars_names bc expr), []);
              } ))
          t spills
      in
      (spills, [ { it = Lam (abs, o, t); loc; ty } ])
  (* holes *)
  | Var (c, xs) ->
      let spills, args = List.split @@ List.map (spill ~types args) xs in
      let args = List.flatten args in
      let spilled = List.flatten spills in
      let it = Var (c, args) in
      let extra = extra + List.length args - List.length xs in
      if is_prop ~extra ty then ([], [ add_spilled ~types spilled { it; loc; ty } ]) else (spilled, [ { it; loc; ty } ])

and spill1 ~types ?extra args ({ loc } as t) =
  let spills, t = spill ~types ?extra args t in
  let t = if List.length t <> 1 then error ~loc "bad pilling" else List.hd t in
  (spills, t)

let rec remove_top_sigmas ~types t =
  match t.it with
  | App ((s, _, _), _ , []) when is_symbol ~types Elpi_runtime.Data.Global_symbols.pi s -> t
  | App ((s,_,_) as n,x,xs) when is_symbol ~types Elpi_runtime.Data.Global_symbols.and_ s ->
      { t with it = App(n,remove_top_sigmas ~types x,smart_map (remove_top_sigmas ~types) xs) }
  | Impl(x,t1,t2) -> { t with it = Impl(x,t1,remove_top_sigmas ~types t2) }
  | App ((s, _, _), ({ it = Lam(Some (_,vn,vty),_,{ loc;ty }); } as b) , []) when is_symbol ~types Elpi_runtime.Data.Global_symbols.sigma s ->
      remove_top_sigmas ~types { loc; ty; it = ScopedTerm.beta b [{ ty = vty; loc; it = Var((Bound elpi_var,vn,vty),[]) }] }
  | _ -> t

let spill ~types t =
  let args = ref 0 in
  (* Format.eprintf "before spill: %a\n" pretty t; *)
  let s, t = spill ~types args t in
  (* Format.eprintf "after spill: %a\n" pp (List.hd t); *)
  let t = List.map (remove_top_sigmas ~types) t in
  (* Format.eprintf "after sigma removal: %a\n" pretty (List.hd t); *)
  (s, t)

let main ~types t =
  (* if needs_spilling then Format.eprintf "before %a\n" pretty t; *)
  let spills, ts = spill ~types (bc_loc [] t) in
  let t =
    match (spills, ts) with
    | [], [ t ] -> t
    | [], _ -> assert false
    | _ :: _, _ -> error ~loc:t.loc "Cannot place spilled expression"
  in
  t
