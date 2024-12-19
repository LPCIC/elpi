open Elpi_util
open Util
open Elpi_parser
open Ast
open Compiler_data

type groundness = IGround | Unknown [@@deriving show]
(* type ctx = { mutable ground : groundness } [@@deriving show] *)
type info = { mutable ground : groundness } [@@deriving show]

let rec check ~is_rule ~type_abbrevs ~kinds ~types:env (t : ScopedTerm.t) ~(exp : TypeAssignment.t) =
  let sigma = ref F.Map.empty in

  let rec get_mode m = match TypeAssignment.deref_tmode m with MVal v -> v | _ -> error "flex mode cannot be get"
  and closed_term ctx ScopedTerm.{ loc; it } =
    match it with
    | CData _ | Const _ | Discard -> ()
    | App (_, _, x, xs) -> List.iter (closed_term ctx) (x :: xs)
    | Impl (_, _, _) -> failwith "TODO"
    | Cast (t, _) -> closed_term ctx t
    | Var (_, _) -> failwith "TODO"
    | Lam (_, _, _, _) -> failwith "TODO"
    | Spill (_, _) -> failwith "TODO"
  and check_mode_args ctx f ty args =
    match (args, ty) with
    | [], _ -> ()
    | x :: xs, TypeAssignment.Arr (m, NotVariadic, l, r) ->
        let m = get_mode m in
        if m = Input then f ctx x;
        check_mode_args ctx f r xs
    | x :: xs, Arr (m, Variadic, _, _) ->
        let m = get_mode m in
        if m = Input then f ctx x;
        check_mode_args ctx f ty xs
    | _ -> anomaly "unreachable branch"
  and check_ground ctx ScopedTerm.{ loc; it } =
    match it with
    | _ -> ()
    | Discard | CData _ | Const (Global _, _) -> ()
    | Const (Bound l, f) -> (
        match Scope.Map.find_opt (f, l) ctx with
        | None -> anomaly "unbound"
        | Some { ground = IGround } -> ()
        | Some _ -> error ~loc (F.show f ^ " not ground " ^ Scope.Map.show pp_info ctx))
    | Var (f, args) -> (
        match F.Map.find_opt f !sigma with
        | None -> anomaly "arg already typed"
        | Some { ground = IGround } -> ()
        | Some _ -> error ~loc (F.show f ^ " not ground: " ^ F.Map.show pp_info !sigma))
    | Cast (t, _) -> check_ground ctx t
    | _ -> ()
    | App (sc, c, x, xs) ->
        let ty = failwith "what is the type of x? get_type returns a overloaded data" (*get_type ~loc sc ctx env c*) in
        check_mode_args ctx check_ground ty (x :: xs)
    | Lam (s, _, tya, bo) ->
        failwith "TODO"
        (* TODO:
           here we can use tya to add the type of s into ctx to the recursive call
           moreover, s is ground or unkown depending on its mode. the mode can
           be found in the ty from the 2nd argument of check_ground
        *)
    | Impl (true, a, b) -> check_ground ctx b (* TODO: check also a*)
    | Impl (false, a, b) -> failwith "TODO"
    | Spill (_, _) -> failwith "TODO"
  and propagate_ground ctx ScopedTerm.{ loc; it } =
    match it with
    | Discard | CData _ | Const (Global _, _) -> ()
    | Const (Scope.Bound l, f) -> (
        match Scope.Map.find_opt (f, l) ctx with
        | None -> anomaly "unbound"
        | Some { ground = IGround } -> ()
        | Some info -> info.ground <- IGround)
    | Var (f, args) -> (
        match F.Map.find_opt f !sigma with
        | None -> anomaly "arg already typed"
        | Some { ground = IGround } -> ()
        | Some info -> info.ground <- IGround)
    | _ -> ()
    | App (s, c, x, xs) ->
        let ty =
          error ~loc
            (Format.asprintf
               "TODO: should get the type of the constant %a, but getting it from the ctx is not good, due to \
                Overloaded symbols..."
               F.pp c)
        in
        check_mode_args ctx propagate_ground ty (x :: xs)
    | Cast (t, _) -> propagate_ground ctx t
    | Impl (_, _, _) -> failwith "TODO"
    | Lam (_, _, _, _) -> failwith "TODO"
    | Spill (_, _) -> failwith "TODO"
  in
  0
