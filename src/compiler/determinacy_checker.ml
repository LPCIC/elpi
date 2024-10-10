(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Elpi_util.Util
open Elpi_parser.Ast
open Compiler_data
module C = Constants

let to_print f = if true then f ()

(* TYPE DECLARATION FOR FUNCTIONALITY *)

type functionality =
  | Functional  (** -> for functional preds *)
  | Relational  (** -> for non-functional preds *)
  | NoProp of functionality list  (** -> for kinds like list, int, string *)
  | BoundVar of F.t  (** -> in predicates like: std.exists or in parametric type abbreviations. *)
  | AssumedFunctional  (** -> variadic predicates: never backtrackc *)
  | Arrow of functionality * functionality  (** -> abstractions *)
  | Any
[@@deriving show, ord]

type functionality_abs =
  | Lam of F.t * functionality_abs  (** e.g: type abbrev (t X) (list X) becomes: Lam A (F (Arrow A NoProp))*)
  | F of functionality
[@@deriving show, ord]

type functionality_loc = Loc.t * functionality_abs [@@deriving show, ord]
type t = { ty_abbr : functionality_loc F.Map.t; cmap : (F.t * functionality) IdPos.Map.t } [@@deriving show, ord]

let arr a b = Arrow (a, b)
let rec bvars2any = function Arrow (l, r) -> arr (bvars2any l) (bvars2any r) | BoundVar _ -> Any | e -> e
let rec eat_lambdas = function Lam (_, b) -> eat_lambdas b | F b -> bvars2any b

type env = t (* This is for the cleaner signatures in this files for objects with type t *)

let compare_functionality_loc a b = compare_functionality_abs (snd a) (snd b)
let compare_fname a b = compare_functionality_loc (snd a) (snd b)
let mk_func_map ty_abbr cmap = { ty_abbr; cmap }
let empty_fmap = { ty_abbr = F.Map.empty; cmap = IdPos.Map.empty }
let get_functionality_tabbr_opt map k = F.Map.find_opt k map.ty_abbr

let rec get_namef = function
  | ScopedTerm.App (_, n, _, _) | Const (_, n) -> n
  | Impl (false, a, _) -> get_namef a.it
  | Var (n, _) -> n
  | e -> error (Format.asprintf "get_name error is not a clause %a" ScopedTerm.pretty_ e)

let functionality_pi_sigma = arr (arr Any Functional) Functional

let get_functionality ~loc ~env k =
  if k = Scope.dummy_type_decl_id then Any
  else
    try
      let name, func = IdPos.Map.find k env.cmap in
      if F.equal F.pif name || F.equal F.sigmaf name then functionality_pi_sigma else func
    with e ->
      Format.eprintf "Error at %a with const %a\n%!" Loc.pp loc IdPos.pp k;
      raise e

(* AUXILIARY FUNCTIONS *)
let rec subst ~loc sigma = function
  | BoundVar k as t -> (
      match F.Map.find_opt k sigma with
      | None -> t
      | Some (F f) -> f
      | Some (Lam (_, b)) -> error ~loc "type_abbrev not fully applied")
  | Arrow (l, r) -> arr (subst ~loc sigma l) (subst ~loc sigma r)
  | NoProp l -> NoProp (List.map (subst ~loc sigma) l)
  | (AssumedFunctional | Functional | Relational | Any) as t -> t

let rec beta ~loc sigma = function
  | Lam (n, b), x :: xs -> beta ~loc (F.Map.add n (F x) sigma) (b, xs)
  | Lam (_, b), [] -> error ~loc "type_abbrev is not fully applied"
  | F t, [] -> subst ~loc sigma t
  | F _, _ :: _ -> anomaly ~loc "type_abbrev is too much applied"

let beta = beta F.Map.empty

(* COMPILATION from SCOPE_TYPE_EXPRESSION TO FUNCTIONALITY *)
module Compilation = struct
  let add_type ~loc is_type_abbr env ~n ~id v =
    if is_type_abbr && F.Map.mem n env.ty_abbr then error (Format.asprintf "Adding again type_abbrev %a" F.pp n);
    if is_type_abbr then
      let ty_abbr = F.Map.add n (loc, v) env.ty_abbr in
      mk_func_map ty_abbr env.cmap
    else
      let cmap = IdPos.Map.add id (n, eat_lambdas v) env.cmap in
      mk_func_map env.ty_abbr cmap

  let merge f1 f2 =
    let pp_fname fmt (x, y) = Format.fprintf fmt "(%a,%a)" F.pp x pp_functionality_loc y in
    let compare_fname (x0, y0) (x1, y1) =
      let cmp = F.compare x0 x1 in
      if cmp = 0 then compare_functionality_loc y0 y1 else cmp
    in
    let union_same pk pe cmpe k e1 e2 =
      (* if cmpe e1 e2 = 0 then  *)
      Some e1
      (* else error (Format.asprintf "The key %a has two different values (v1:%a) (v2:%a)" pk k pe e1 pe e2)  *)
    in
    let cmap = IdPos.Map.union (union_same pp_int pp_fname compare_fname) f1.cmap f2.cmap in
    let ty_abbr = F.Map.union (union_same F.pp pp_int Int.compare) f1.ty_abbr f2.ty_abbr in
    mk_func_map ty_abbr cmap

  let rec arr2list = function ScopedTypeExpression.Arrow (_, l, r) -> l.it :: arr2list r.it | e -> []
  let rec fold last f = function [] -> last | x :: xs -> arr (f x) (fold last f xs)
  let apply_snd f (_, a) = f a

  let rec type2func_ty_abbr ~pfile ~loc bound_vars (env : env) c args =
    match get_functionality_tabbr_opt env c with
    | None ->
        (* -> c is a kind (like list, int, ...) *)
        NoProp (List.map (type2func_loc ~pfile ~loc bound_vars env) args)
    | Some (_, f) ->
        (* -> c is a type-abbrev *)
        beta ~loc (f, List.map (type2func_loc ~pfile ~loc bound_vars env) args)

  and type2func ~pfile ~loc bound_vars (env : env) = function
    | ScopedTypeExpression.Pred (Function, xs) ->
        fold Functional (apply_snd @@ type2func_loc ~pfile ~loc bound_vars env) xs
    | Pred (Relation, xs) -> fold Relational (apply_snd @@ type2func_loc ~pfile ~loc bound_vars env) xs
    | Const (_, c) when F.Set.mem c bound_vars -> BoundVar c
    | Const (_, c) -> type2func_ty_abbr ~pfile ~loc bound_vars env c []
    | App (c, x, xs) -> type2func_ty_abbr ~pfile ~loc bound_vars env c (x :: xs)
    | Arrow (Variadic, _, _) -> AssumedFunctional
    (* Invariant: the rightmost type in the right branch is not a prop due flatten_arrows in compiler *)
    | Arrow (NotVariadic, l, r) ->
        arr (type2func_loc ~pfile ~loc bound_vars env l) (type2func_loc ~pfile ~loc bound_vars env r)
    | Any -> Any

  and type2func_loc ~pfile ~loc bvars env ScopedTypeExpression.{ it } = type2func ~pfile ~loc bvars env it

  let rec type2func_lam ~pfile bound_vars type_abbrevs = function
    | ScopedTypeExpression.Lam (n, t) ->
        let loc, r = type2func_lam ~pfile (F.Set.add n bound_vars) type_abbrevs t in
        (loc, Lam (n, r))
    | Ty { it; loc } -> (loc, F (type2func ~pfile ~loc bound_vars type_abbrevs it))

  let type2func env (x : ScopedTypeExpression.t) = type2func_lam F.Set.empty env x.value ~pfile:None
end

let merge = Compilation.merge

let rec functionality_leq ~loc a b =
  match (a, b) with
  | NoProp _, x -> functionality_leq ~loc Any x
  | x, NoProp _ -> functionality_leq ~loc x Any
  | _, Any -> true
  | Any, _ -> false
  | BoundVar _, _ | _, BoundVar _ -> true (* TODO: this is not correct... -> use ref with uvar to make unification *)
  | _, Relational -> true
  | Relational, _ -> false
  | Functional, Functional -> true
  | AssumedFunctional, _ -> true
  | _, AssumedFunctional -> error ~loc (Format.asprintf "Cannot compare AssumedFunctional with different functionality")
  | Arrow (l1, r1), Arrow (l2, r2) -> functionality_leq ~loc l2 l1 && functionality_leq ~loc r1 r2
  | Arrow _, _ | _, Arrow _ ->
      error ~loc (Format.asprintf "Type error1 in comparing %a and %a" pp_functionality a pp_functionality b)
(* | NoProp _, _ | _, NoProp _ -> error ~loc "Type error2" *)

let functionality_leq ~loc a b =
  let res = functionality_leq ~loc a b in
  Format.eprintf "Going to compare %a and %a = %b@." pp_functionality a pp_functionality b res;
  res

let functionality_leq_error ~loc ?(pref = "") a b =
  if not (functionality_leq ~loc a b) then
    error ~loc
      (Format.asprintf "[%s] Functionality error at %a is not less then %a" pref pp_functionality a pp_functionality b)

let split_bang t =
  let rec split_bang_list bef aft = function
    | [] -> (bef, aft)
    | x :: xs ->
        let bef, aft = split_bang bef aft x in
        split_bang_list bef aft xs
  and split_bang bef aft (ScopedTerm.{ it } as t) =
    match it with
    | Const (_, t) when F.equal F.cutf t -> (List.append bef (List.rev aft), [])
    | App (_, hd, x, xs) when F.equal F.andf hd -> split_bang_list bef aft (x :: xs)
    | _ -> (bef, t :: aft)
  and split_bang_loc bef aft t = split_bang bef aft t in
  let bef, aft = split_bang_loc [] [] t in
  (bef, List.rev aft)

let min ~loc f1 f2 = if functionality_leq ~loc f1 f2 then f1 else f2
let max ~loc f1 f2 = if functionality_leq ~loc f1 f2 then f2 else f1

module EnvMaker (M : Map.S) : sig
  type t [@@deriving show]

  val add : loc:Loc.t -> v:functionality -> t -> M.key -> t
  val get : t -> M.key -> functionality option
  val mem : t -> M.key -> bool
  val empty : t
end = struct
  type t = functionality ref M.t [@@deriving show]

  let add ~loc ~(v : functionality) (env : t) (n : M.key) : t =
    match M.find_opt n env with
    | None -> M.add n (ref v) env
    | Some v' ->
        (* functionality_leq_error ~loc ~pref:("Adding setted var " ^ M.show_key n) v !v'; *)
        v' := min ~loc v !v';
        env

  let get (env : t) (k : M.key) =
    try Option.map (fun x -> !x) (M.find_opt k env)
    with e ->
      Format.eprintf "Cannot find the key %a in the map\n" M.pp_key k;
      raise e

  let mem env k = M.mem k env
  let empty = M.empty
end

module Env = EnvMaker (F.Map)
module Ctx = EnvMaker (Scope.Map)

let eat_abs ~loc = function
  | AssumedFunctional -> (Any, AssumedFunctional)
  | Any -> (Any, Any)
  | Arrow (l, r) -> (l, r)
  | BoundVar _ -> error ~loc "TODO:?"
  | _ -> error ~loc "Type error3"

let not_functional_call_error ~loc t =
  error ~loc (Format.asprintf "Non functional premise call %a\n" ScopedTerm.pretty_ t)

module Checker_clause = struct
  let check ~modes ~(global : env) ~loc tm =
    let env = ref Env.empty in
    let pp_env fmt () : unit = Format.fprintf fmt "Env : %a" Env.pp !env in
    let add_env ~v n = env := Env.add ~loc !env ~v n in
    let not_mem n = Env.mem !env n |> not in
    let add_ctx ctx ~v n = Ctx.add ~loc ctx ~v n in

    let get_mode c =
      match F.Map.find_opt c modes with
      | None -> error ~loc (Format.asprintf "Cannot find mode for %a" F.pp c)
      | Some (e, _) -> List.map (function Fo m | Ho (m, _) -> m) e
    in

    let rec fold_left_partial f acc args modes =
      match (args, modes) with
      | [], _ -> acc
      | x :: xs, y :: ys -> fold_left_partial f (f acc x y) xs ys
      | _ :: _, [] -> error ~loc:tm.ScopedTerm.loc "Invalid application"
    in

    let fold_on_modes input output tm args modes =
      fold_left_partial
        (fun func arg mode ->
          match func with
          | Any -> Any
          | Arrow (l, r) -> if mode = Input then input arg l r else output arg l r
          | _ -> error ~loc:arg.ScopedTerm.loc "Type error")
        tm args modes
    in

    let get_funct_of_term ctx = function
      | ScopedTerm.Var (v, args) -> Env.get !env v
      | Const (Global { decl_id }, _) ->
          Some (match get_functionality ~loc ~env:global decl_id with Relational -> Functional | e -> e)
      | App (Global { decl_id }, _, _, _) -> Some (get_functionality ~loc ~env:global decl_id)
      | App (Bound scope, f, _, _) | Const (Bound scope, f) -> Ctx.get ctx (f, scope)
      | CData _ -> Some (NoProp [])
      | Spill _ -> error ~loc "get_funct_of_term of spilling: "
      | e -> error ~loc (Format.asprintf "get_funct_of_term %a" ScopedTerm.pp_t_ e)
    in

    let get_func_hd ctx t =
      let rec get_right_most = function Arrow (_, r) -> get_right_most r | e -> e in
      Option.value ~default:Any (get_funct_of_term ctx t) |> get_right_most
    in

    let functionality_beta f args ctx =
      Format.eprintf "To be reduced: %a applied to the func of %a in env: %a@." pp_functionality f
        (pplist ScopedTerm.pretty ",,,, ") args pp_env ();
      let xs = List.map (fun ScopedTerm.{ it } -> get_funct_of_term ctx it) args in
      let rec aux = function
        | Some x :: xs, _ :: args, Arrow (l, r) ->
            Format.eprintf "x is %a and l is %a\n" pp_functionality x pp_functionality l;
            if functionality_leq ~loc x l then aux (xs, args, r) else Any
        | None :: xs, ScopedTerm.{ it = Var (name, _args) } :: args, Arrow ((NoProp _ as np), r) ->
            (* TODO: consider args... *)
            add_env name ~v:np;
            aux (xs, args, r)
        | None :: xs, _, _ -> Any
        | [], _, f -> f
        | _ -> error ~loc "Type error4"
      in
      aux (xs, args, f)
    in

    let rec unify_func (t1 : ScopedTerm.t_) (t2 : ScopedTerm.t_) (ctx : Ctx.t) : unit =
      match (t1, t2) with
      (* No var is set *)
      | Var (_n, _args), Var (_n1, args1) when not_mem _n && not_mem _n1 ->
          error ~loc (Format.asprintf "Var-var case in unfy-func v1:%a - v2:%a" ScopedTerm.pp_t_ t1 ScopedTerm.pp_t_ t2)
      (* Left var is set *)
      | Var (_n, _args), Var (_n1, args1) when not_mem _n1 ->
          add_env
            ~v:(get_funct_of_term ctx t1 |> Option.get)
            _n1 (* TODO: THIS IS WRONG: SHOULD TAKE INTO ACCOUNT THE ARGS OF BOTH VARS... *)
      (* Right var is set *)
      | Var (_n, _args), Var (_n1, args1) when not_mem _n ->
          add_env
            ~v:(get_funct_of_term ctx t2 |> Option.get)
            _n (* TODO: THIS IS WRONG: SHOULD TAKE INTO ACCOUNT THE ARGS OF BOTH VARS... *)
      (* Both var are set *)
      | Var (_n, _args), Var (_n1, args1) -> assert (get_funct_of_term ctx t1 = get_funct_of_term ctx t2)
      (* TODO: THIS IS WRONG: SHOULD TAKE INTO ACCOUNT THE ARGS OF BOTH VARS... *)
      (* The variable is not set *)
      | Var (vname, args), App (_, n, x, xs) when not_mem vname ->
          Format.eprintf "Going to make beta reduction of %a with func = %a@." F.pp n pp_functionality
            (get_funct_of_term ctx t2 |> Option.get);
          let v = functionality_beta (get_funct_of_term ctx t2 |> Option.get) (x :: xs) ctx in
          Format.eprintf "Beta reduced functionality is %a@." pp_functionality v;
          add_env vname ~v
      | Var (vname, args), Const _ when not_mem vname -> add_env vname ~v:(get_funct_of_term ctx t2 |> Option.get)
      (* The variable is set into the dict *)
      | Var (vname, args), App (_, n, x, xs) ->
          let func_t2 = get_funct_of_term ctx t2 |> Option.get in
          Format.eprintf "Functionality unification of %a and %a@." ScopedTerm.pretty_ t1 ScopedTerm.pretty_ t2;
          let v = functionality_beta func_t2 (x :: xs) ctx in
          Format.eprintf "Beta reduced functionality is %a@." pp_functionality v;
          add_env vname ~v
      | Var (vname, args), Const _ -> add_env vname ~v:(get_funct_of_term ctx t2 |> Option.get)
      (* Swap call *)
      | x, Var _ when not (ScopedTerm.is_var x) -> unify_func t2 t1 ctx
      | _ ->
          error ~loc
            (Format.asprintf "trying to unify \n- %a and \n- %a in \n %a@." ScopedTerm.pretty_ t1 ScopedTerm.pretty_ t2
               pp_env ())
    in

    let check_head_input =
      let rec build_hyps_head_aux ctx = function
        | [], _ -> ()
        | ScopedTerm.{ it } :: tl, Arrow (l, r) ->
            build_hyp_head ctx l it;
            build_hyps_head_aux ctx (tl, r)
        | _ :: _, _ -> anomaly "Type error5"
      and build_hyp_head (ctx : Ctx.t) (assumed : functionality) (t : ScopedTerm.t_) =
        match t with
        | ScopedTerm.Const _ | Discard | CData _ -> ()
        | Var (n, _args) -> add_env n ~v:assumed
        | Lam (None, _, _type, { it }) -> build_hyp_head ctx (eat_abs ~loc assumed |> snd) it
        | Lam (Some x, _, _type, { it }) ->
            let v, assumed = eat_abs ~loc assumed in
            build_hyp_head (add_ctx ctx x ~v) assumed it (* TODO: Here I use any instead of Relational ...*)
        | Impl (true, _hd, { it }) -> () (* TODO: this is ignored *)
        | Impl (false, _, _) -> () (* TODO: this is ignored *)
        | App (_, n, x, [ y ]) when F.equal F.isf n || F.equal F.eqf n -> unify_func x.it y.it ctx
        (* | App (_, n, x, [ y ]) when F.equal F.isf n || F.equal F.eqf n -> unify_func x.it y.it ctx *)
        | App (_, n, x, xs) -> (
            to_print (fun () ->
                Format.eprintf ".The global app is %a and its functionality is %a@." F.pp n
                  (Format.pp_print_option pp_functionality)
                  (get_funct_of_term ctx t));
            match get_funct_of_term ctx t with
            | None -> () (* TODO: The functionality of t is not already known... should be taken into account *)
            | Some e -> (
                (* TODO: check functionality of e is leq of exp: otherwise we can raise a warning? *)
                (* TODO: in the head, if we expect a relational prop, and we destruct a functional term, then all args of the term are relational *)
                match e with
                | Any | BoundVar _ | AssumedFunctional ->
                    build_hyps_head_aux ctx (x :: xs, List.fold_right (fun _ acc -> arr Any acc) (x :: xs) Any)
                | Functional | Relational | NoProp _ -> assert false
                | Arrow (l, r) -> build_hyps_head_aux ctx (x :: xs, e)))
        | Cast ({ it }, _) -> build_hyp_head ctx assumed it
        | Spill _ -> error ~loc "Spill in the head"
      and build_hyps_head_modes ctx func args modes = match args, func, modes with
        | [],_,_ -> ()
        | arg::args, Arrow (l,r), Input :: modes ->
          build_hyp_head ctx l arg.ScopedTerm.it;
          build_hyps_head_modes ctx r args modes
        | _::args, Arrow (_,r), Output :: modes ->
          build_hyps_head_modes ctx r args modes
        | _, _, _ -> error ~loc (Format.asprintf "Type error %a [%a] [%a]" pp_functionality func (pplist ScopedTerm.pretty ",") args (pplist pp_arg_mode ",") modes)

        (* fold_on_modes (fun t l r -> 
          build_hyp_head ctx l t.ScopedTerm.it; Functional)
          (fun _ _ _ -> Any) *)
      and build_hyps_head (ctx : Ctx.t) (t : ScopedTerm.t_) =
        match t with
        | ScopedTerm.Const _ -> ()
        | App (Global { decl_id }, f, x, xs) -> (
            match get_funct_of_term ctx t with
            | None -> assert false (* TODO: The functionality is not know... *)
            | Some e -> 
                Format.eprintf "Before call to build_hyps_head_modes, func is %a@." pp_functionality e;
                build_hyps_head_modes ctx e (x :: xs) (get_mode f) |> ignore )
        | App (Bound _, f, _, _) -> error ~loc (Format.asprintf "No signature for predicate %a@." F.pp f)
        | Var _ -> error ~loc "Flex term used has head of a clause"
        | _ -> failwith "type error7"
      in
      build_hyps_head
    in

    let check_body ctxx tm exp : unit =
      let rec func2mode = function Arrow (_, r) -> Output :: func2mode r | _ -> [] in
      let get_mode n f = try get_mode n with _ -> func2mode f in
      let rec infer_app n ctx t args =
        to_print (fun () -> Format.eprintf "The global app is %a@." F.pp n);
        match get_funct_of_term ctx t with
        | None ->
            error ~loc (Format.asprintf "TODO2 %a" pp_env ())
            (* TODO: The functionality of t is not known... should be taken into account *)
        | Some e ->
            let modes = get_mode n e in

            Format.eprintf "The functionality of %a is %a@." F.pp n pp_functionality e;
            let valid_call = valid_call ctx e args modes in

            Format.eprintf "Valid call for %a is %a@." F.pp n pp_functionality valid_call;

            if valid_call <> Any then infer_outputs ctx e args modes
            else (
              infer_outputs_fail ctx e args modes |> ignore;
              Any)
      and valid_call ctx =
        fold_on_modes
          (fun e l r ->
            let inferred = infer ctx e in
            if functionality_leq ~loc:e.ScopedTerm.loc inferred l then r else Any)
          (fun _ _ r -> r)
      and infer_outputs ctx =
        fold_on_modes
          (fun _ _ r -> r)
          (fun e l r ->
            let inferred = infer ctx e in
            Format.eprintf "Before setting %a and l is %a@." ScopedTerm.pretty e pp_functionality l;
            match e.ScopedTerm.it with
            | Var (n, []) ->
                add_env n ~v:l;
                r
            | _ -> if functionality_leq ~loc:e.loc inferred l then r else Any)
      and infer_outputs_fail ctx =
        fold_on_modes
          (fun _ _ r -> r)
          (fun e l r ->
            match e.ScopedTerm.it with
            | Var (n, []) ->
                add_env n ~v:Any;
                r
            | _ -> assert false)
      and infer ctx ({ it = t; loc } : ScopedTerm.t) : functionality =
        match t with
        | ScopedTerm.Const _ | CData _ -> get_funct_of_term ctx t |> Option.get
        | Discard -> Functional
        | Var (n, []) -> ( match Env.get !env n with None -> Any | Some e -> e)
        | Var (n, args) -> infer_app n ctx t args
        | Lam (None, _, _type, t) -> arr Any (infer ctx t)
        | Lam (Some vname, _, _type, t) -> arr Any (infer (add_ctx ctx vname ~v:Any) t)
        | Impl (true, _hd, t) -> infer ctx t (* TODO: hd is ignored *)
        | Impl (false, _, t) -> infer ctx t (* TODO: this is ignored *)
        | App (_, n, x, [ y ]) when F.equal F.isf n || F.equal F.eqf n ->
            unify_func x.it y.it ctx;
            Functional
        | App (_, n, x, xs) when F.equal F.andf n ->
            let args = x :: xs in
            List.fold_right (fun e acc -> infer ctx e |> max ~loc:e.ScopedTerm.loc acc) args Functional
        | App (_, n, x, []) when F.equal F.pif n || F.equal F.sigmaf n -> (
            match infer ctx x with
            | Arrow (_, r) -> r
            | e -> error ~loc (Format.asprintf "Type error (%a is not a function)" ScopedTerm.pretty_ t))
        | App (_, n, x, xs) -> (
            to_print (fun () -> Format.eprintf "The global app is %a@." F.pp n);
            match get_funct_of_term ctx t with
            | None ->
                error ~loc "TODO22" (* TODO: The functionality of t is not known... should be taken into account *)
            | Some e -> infer_app n ctx t (x :: xs))
        | Cast (t, _) -> infer ctx t
        | Spill (a, b) -> error ~loc "TODO3" (* error ~loc "Spill NYI" *)
      and check ctx (t : ScopedTerm.t) (exp : functionality) : unit =
        let before, after = split_bang t in
        List.iter (fun e -> infer ctx e |> ignore) before;

        List.iter
          (fun e ->
            let inferred = infer ctx e in
            Format.eprintf "Inferred is %a and expected is %a@." pp_functionality inferred pp_functionality exp;
            functionality_leq_error ~loc:e.ScopedTerm.loc inferred exp)
          after
      in

      check ctxx tm exp
    in

    let main ctx (tm : ScopedTerm.t_) : unit =
      let hd, body =
        match tm with
        | App _ | Const _ -> (tm, None)
        | Impl (false, hd, body) -> (hd.it, Some body)
        | Var _ -> failwith "flexible clause..."
        | _ -> failwith "Type error8"
      in
      Format.eprintf "=====================================================@.";
      to_print (fun () -> Format.eprintf "The head is `%a`@." ScopedTerm.pretty_ hd);
      check_head_input ctx hd;
      Format.eprintf "END HEAD CHECK@.";

      to_print (fun () -> Format.eprintf "The contex_head is %a@." pp_env ());
      Option.iter (fun body -> check_body ctx body (get_func_hd ctx hd)) body
    in
    main Ctx.empty tm.it
end

let to_check_clause ScopedTerm.{ it; loc } =
  let n = get_namef it in
  false && (not (F.equal n F.mainf)) && Re.Str.string_match (Re.Str.regexp ".*test.*") (Loc.show loc) 0

let check_clause ~loc ~env ~modes t =
  if to_check_clause t then (
    (* check_clause ~loc ~env F.Map.empty t |> ignore *)
    Format.eprintf "============== STARTING mode checking@.";
    (* Format.eprintf "Modes are [%a]" (F.Map.pp (fun fmt ((e:mode_aux list),_) -> Format.fprintf fmt "%a" pp_mode e)) (modes); *)
    (* Format.eprintf "Functional preds are %a@." pp env; *)
    Checker_clause.check ~modes ~global:env ~loc t)

class merger (all_func : env) =
  object (self)
    val mutable all_func = all_func
    val mutable local_func = empty_fmap

    method private add_func is_ty_abbr id ty =
      let loc, func = Compilation.type2func all_func ty in
      let n = ty.name in
      (* Format.eprintf "Adding constant %a with id %i\n%!" F.pp n id; *)
      if is_ty_abbr then all_func <- Compilation.add_type ~loc is_ty_abbr ~id ~n all_func func;
      local_func <- Compilation.add_type ~loc is_ty_abbr ~id ~n local_func func

    method get_all_func = all_func
    method get_local_func = local_func
    method add_ty_abbr = self#add_func true

    method add_func_ty_list ty (ty_w_id : TypeAssignment.overloaded_skema_with_id) =
      let id_list = match ty_w_id with Single e -> [ fst e ] | Overloaded l -> List.map fst l in
      List.iter2 (self#add_func false) id_list ty

    method merge : env = merge all_func local_func
  end

module Test = struct
  let global_default = Scope.Global { escape_ns = false; decl_id = Scope.dummy_type_decl_id }
  let addloc2te it = ScopedTypeExpression.{ it; loc = Loc.initial "" }

  let build_full_te name value =
    ScopedTypeExpression.{ value; loc = Loc.initial ""; indexing = None; nparams = 0; name }

  let const e = addloc2te (Const (global_default, e))
  let mkapp n args = addloc2te @@ App (n, List.hd args, List.tl args)
  let pred l = addloc2te (Pred (Relation, List.map (fun e -> (Mode.Output, e)) l))
  let arrta a b = TypeAssignment.Arr (NotVariadic, a, b)
  let boolf = F.from_string "bool"

  let%test "test_type2func" =
    let builder = new merger empty_fmap in

    (* Typeabbrev ta: (A\ A -> A -> prop) *)
    let ta_id, ta =
      let fA = F.from_string "A" in
      let constA = addloc2te (Const (Bound "elpi", fA)) in
      let ta_id = IdPos.make_str "ta_id" in
      let ta_name = F.from_string "ta_name" in
      let ty = ScopedTypeExpression.(Lam (fA, Ty (pred [ constA; constA ]))) in
      (ta_id, build_full_te ta_name ty)
    in

    (* pred p i:(ta bool) *)
    let ty_id, tyexpr, ty_overloading =
      let ty = ScopedTypeExpression.Ty (pred [ mkapp ta.name [ const boolf ] ]) in

      let ty_name = F.from_string "ty_name" in
      let ty_id = IdPos.make_str "ty_id" in

      let tyos = TypeAssignment.(Single (ty_id, Ty (arrta (Cons boolf) (arrta (Cons boolf) Prop)))) in
      (ty_id, [ build_full_te ty_name ty ], tyos)
    in

    builder#add_ty_abbr ta_id ta;
    builder#add_func_ty_list tyexpr ty_overloading;

    let all_func = builder#merge in
    IdPos.Map.find ty_id all_func.cmap |> snd = arr (arr (NoProp []) (arr (NoProp []) Relational)) Relational
end
