(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Elpi_util.Util
open Elpi_parser.Ast
open Compiler_data
module C = Constants
module Union_find = Union_find.Make (IdPos.Map)

let to_print f = if false then f ()

(* TYPE DECLARATION FOR FUNCTIONALITY *)

type functionality =
  | Functional  (** -> for functional preds *)
  | Relational  (** -> for non-functional preds *)
  | NoProp of functionality list  (** -> for kinds like list, int, string *)
  | BoundVar of F.t  (** -> in predicates like: std.exists or in parametric type abbreviations. *)
  | AssumedFunctional  (** -> variadic predicates: never backtrack *)
  | Arrow of Mode.t * functionality * functionality  (** -> abstractions *)
  | Any
[@@deriving show, ord]

type functionality_abs =
  | Lam of F.t * functionality_abs  (** e.g: type abbrev (t X) (list X) becomes: Lam A (F (Arrow A NoProp))*)
  | F of functionality
[@@deriving show, ord]

type functionality_loc = Loc.t * functionality_abs [@@deriving show, ord]
type t = { ty_abbr : functionality_loc F.Map.t; cmap : (F.t * functionality) IdPos.Map.t } [@@deriving show, ord]

let arr m a b = Arrow (m, a, b)
let is_NoProp = function NoProp _ -> true | _ -> false

let rec pp_functionality fmt = function
  | Functional -> Format.fprintf fmt "F"
  | Relational -> Format.fprintf fmt "R"
  | AssumedFunctional -> Format.fprintf fmt "AF"
  | Any -> Format.fprintf fmt "Any"
  | BoundVar b -> Format.fprintf fmt "BV %a" F.pp b
  | Arrow (m, a, b) -> Format.fprintf fmt "(%a:%a -> %a)" Mode.pp_short m pp_functionality a pp_functionality b
  | NoProp l -> Format.fprintf fmt "Kind [@[%a@]]" (pplist pp_functionality ",") l

let get_NoProp_list ~loc = function
  | NoProp l -> l
  | e -> error ~loc (Format.asprintf "get_NoProp_list: got %a" pp_functionality e)

(* let rec bvars2any = function Arrow (l, r) -> arr (bvars2any l) (bvars2any r) | BoundVar _ -> Any | e -> e *)
let rec eat_lambdas = function Lam (_, b) -> eat_lambdas b | F b -> b

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

let functionality_pi_sigma = arr Output (arr Output Any Functional) Functional

(* AUXILIARY FUNCTIONS *)
let rec subst ~loc sigma = function
  | BoundVar k as t -> (
      match F.Map.find_opt k sigma with
      | None -> t
      | Some (F f) -> f
      | Some (Lam (_, b)) -> error ~loc "type_abbrev not fully applied")
  | Arrow (m, l, r) -> arr m (subst ~loc sigma l) (subst ~loc sigma r)
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

  module ScopeTE = struct
    let rec fold last f = function [] -> last | (m,x) :: xs -> arr m (f x) (fold last f xs)

    let rec type2func_ty_abbr ~pfile ~loc bound_vars (env : env) c args =
      match get_functionality_tabbr_opt env c with
      | None ->
          (* -> c is a kind (like list, int, ...) *)
          NoProp (List.map (type2func_loc ~pfile ~loc bound_vars env) args)
      | Some (_, f) ->
          (* -> c is a type-abbrev *)
          beta ~loc (f, List.map (type2func_loc ~pfile ~loc bound_vars env) args)

    and type2func ~pfile ~loc bound_vars (env : env) = function
      | ScopedTypeExpression.Const (_, c) when F.Set.mem c bound_vars -> BoundVar c
      | Const (_, c) -> type2func_ty_abbr ~pfile ~loc bound_vars env c []
      | App (c, x, xs) -> type2func_ty_abbr ~pfile ~loc bound_vars env c (x :: xs)
      | Arrow (_, Variadic, _, _) -> AssumedFunctional (* TODO: should take into account the mode? *)
      (* Invariant: the rightmost type in the right branch is not a prop due flatten_arrows in compiler *)
      | Arrow (m, NotVariadic, l, r) ->
          arr m (type2func_loc ~pfile ~loc bound_vars env l) (type2func_loc ~pfile ~loc bound_vars env r)
      | Any -> Any
      | Prop Function -> Functional
      | Prop Relation -> Relational

    and type2func_loc ~pfile ~loc bvars env ScopedTypeExpression.{ it } = type2func ~pfile ~loc bvars env it

    let rec type2func_lam ~pfile bound_vars type_abbrevs = function
      | ScopedTypeExpression.Lam (n, t) ->
          let loc, r = type2func_lam ~pfile (F.Set.add n bound_vars) type_abbrevs t in
          (loc, Lam (n, r))
      | Ty { it; loc } -> (loc, F (type2func ~pfile ~loc bound_vars type_abbrevs it))

    let type2func env (x : ScopedTypeExpression.t) = type2func_lam F.Set.empty env x.value ~pfile:None
  end

  module TypeAssignment : sig
    val type_ass_2func : ?ag:ScopedTerm.t list -> loc:Loc.t -> env -> TypeAssignment.t MutableOnce.t -> functionality
    val build_app_ty : TypeAssignment.t MutableOnce.t -> ScopedTerm.t list -> TypeAssignment.t MutableOnce.t
  end = struct
    let get_mutable v = match MutableOnce.get v with TypeAssignment.Val v -> v

    (*
       Build the type of the head a term application.
       For example:
         app(f, x, xs): the type of f is `x.ty -> xs_1.ty -> ... -> xs_n.ty -> (app(f,x,xs)).ty
         v(X, args): the type of X is `args_1.ty -> ... -> xs_n.ty -> (v(X,args)).ty
    *)
    let rec build_app_ty ty = function
      | [] -> ty
      | ScopedTerm.{ ty } :: xs ->
          let left = if MutableOnce.is_set ty then get_mutable ty else UVar ty in
          let right = get_mutable @@ build_app_ty ty xs in
          MutableOnce.create (TypeAssignment.Val (Arr (Output, NotVariadic, left, right)))

    let rec type2func_ty_abbr ~pfile ~loc (env : env) c args =
      match get_functionality_tabbr_opt env c with
      | None ->
          (* -> c is a kind (like list, int, ...) *)
          NoProp (List.map (type_ass_2func ~pfile ~loc env) args)
      | Some (_, f) ->
          (* -> c is a type-abbrev *)
          beta ~loc (f, List.map (type_ass_2func ~pfile ~loc env) args)

    and type_ass_2func ~pfile ~loc (env : env) = function
      | TypeAssignment.Prop Function -> Functional
      | TypeAssignment.Prop Relation -> Relational
      | Any -> Any
      | Cons n -> type2func_ty_abbr ~pfile ~loc env n []
      | App (n, x, xs) -> type2func_ty_abbr ~pfile ~loc env n (x :: xs)
      | Arr (_,Variadic, _, _) -> AssumedFunctional
      | Arr (m,NotVariadic, l, r) -> arr m (type_ass_2func ~pfile ~loc env l) (type_ass_2func ~pfile ~loc env r)
      | UVar a ->
          if MutableOnce.is_set a then type_ass_2func ~pfile ~loc (env : env) (get_mutable a)
          else BoundVar (MutableOnce.get_name a)

    let type_ass_2func ?(ag = []) ~loc env t =
      let t = build_app_ty t ag in
      type_ass_2func ~loc env (get_mutable t) ~pfile:None
  end
end

let merge = Compilation.merge
let remove t k = { t with cmap = IdPos.Map.remove k t.cmap }

let get_functionality ~uf ?tyag ~loc ~env id =
  if id = Scope.dummy_type_decl_id then Any
  else
    let id' = Union_find.find uf id in
    if id <> id' then assert (not (IdPos.Map.mem id env.cmap));
    (* Sanity check *)
    match IdPos.Map.find_opt id' env.cmap with
    | None -> (
        (* TODO: this is temporary: waiting for unknown type to be added in the
            type db After that change, the match becomes useless and ~tyag can
            be removed from the parameters of get_functionality
        *)
        match tyag with
        | None -> error ~loc (Format.asprintf "Cannot find functionality of id %a\n%!" IdPos.pp id')
        | Some (ty, ag) -> Compilation.TypeAssignment.type_ass_2func ~ag ~loc env ty)
    | Some (name, func) -> if F.equal F.pif name || F.equal F.sigmaf name then functionality_pi_sigma else func

let rec all_relational = function
  | BoundVar _ -> true (* TODO: not sure of this? *)
  | Relational -> true
  | Arrow (_, l, r) -> all_relational l && all_relational r
  | Functional -> false
  | NoProp l -> List.for_all all_relational l
  | AssumedFunctional -> false
  | Any -> true

let ( <<= ) ~loc a b =
  let rec aux ~loc a b =
    match (a, b) with
    | BoundVar _, _ | _, BoundVar _ -> true (* TODO: this is not correct... -> use ref with uvar to make unification *)
    | NoProp _, x -> aux Any x ~loc
    | x, NoProp _ -> aux x Any ~loc
    | _, Any -> true
    | Any, _ -> all_relational b
    | _, Relational -> true
    | Relational, _ -> false
    | Functional, Functional -> true
    | AssumedFunctional, _ -> true
    | _, AssumedFunctional ->
        error ~loc (Format.asprintf "Cannot compare AssumedFunctional with different functionality")
    | Arrow (m1, l1, r1), Arrow (m2, l2, r2) -> aux l2 l1 ~loc && aux r1 r2 ~loc
    | Arrow _, _ | _, Arrow _ ->
        error ~loc (Format.asprintf "Type error1 in comparing %a and %a" pp_functionality a pp_functionality b)
    (* | NoProp _, _ | _, NoProp _ -> error ~loc "Type error2" *)
  in
  let res = aux a b ~loc in
  to_print (fun () -> Format.eprintf "%a <= %a = %b@." pp_functionality a pp_functionality b res);
  res

let functionality_leq_error ~loc ?(pref = "") a b =
  if not ((a <<= b) ~loc) then
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
    | Const (Global _, t) when F.equal F.cutf t -> (List.append bef (List.rev aft), [])
    | App (Global _, hd, x, xs) when F.equal F.andf hd -> split_bang_list bef aft (x :: xs)
    | _ -> (bef, t :: aft)
  and split_bang_loc bef aft t = split_bang bef aft t in
  let bef, aft = split_bang_loc [] [] t in
  (bef, List.rev aft)

let cmp ~loc f1 f2 =
  let b1 = (f1 <<= f2) ~loc in
  let b2 = (f2 <<= f1) ~loc in
  match (b1, b2) with
  | true, true -> 0
  | true, false -> -1
  | false, true -> 1
  | false, false ->
      error ~loc (Format.asprintf "Functionality %a and %a are not comparable" pp_functionality f1 pp_functionality f2)

(* R e adesso so che è F -> F *)
(* p X, q X *)

(*  *)
let min ~loc f1 f2 = if cmp ~loc f1 f2 <= 0 then f1 else f2
let max ~loc f1 f2 = if cmp ~loc f1 f2 <= 0 then f2 else f1

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
  | Arrow (_, l, r) -> (l, r)
  | BoundVar _ -> error ~loc "TODO:?"
  | _ -> error ~loc "Type error3"

let not_functional_call_error ~loc t =
  error ~loc (Format.asprintf "Non functional premise call %a\n" ScopedTerm.pretty_ t)

module Checker_clause = struct
  let check ?(uf = Union_find.empty) ~(global : env) tm =
    let env = ref Env.empty in
    let pp_env fmt () : unit = Format.fprintf fmt "Env : %a" Env.pp !env in
    (* let pp_ctx fmt ctx : unit = Format.fprintf fmt "Ctx : %a" Ctx.pp ctx in *)
    let add_env ~loc ~v n = env := Env.add ~loc !env ~v n in
    (* let not_mem n = Env.mem !env n |> not in *)
    let add_ctx ~loc ctx ~v n = Ctx.add ~loc ctx ~v n in

    (* let rec fold_left_partial f acc args =
      match (args) with
      | [] -> acc
      | a :: xs -> fold_left_partial f (f acc a) xs *)
      (* Below the case of variadic functions like var. We assume all
         args to be in output mode
      *)
      (* | a :: xs -> AssumedFunctional *)
      (* | a :: xs, [] -> fold_left_partial f (f acc a Output) xs [] *)
      (* | _ :: _, [] -> error ~loc:tm.ScopedTerm.loc "fold_left_partial: Invalid application" *)
    (* in *)

    let fold_on_modes input output func args =
      to_print (fun () ->
          Format.eprintf "Folding of @[%a@] with args @[%a@]@." pp_functionality func
            (pplist ScopedTerm.pretty ",") args);
      List.fold_left
        (fun func arg ->
          match func with
          | Any | BoundVar _ -> Any
          | Arrow (Input, l, r) -> input arg l r
          | Arrow (Output, l, r) -> output arg l r
          | _ -> error ~loc:arg.ScopedTerm.loc (Format.asprintf "Type error fold modes, found %a" pp_functionality func))
        func args
    in

    let get_funct_of_term ctx ScopedTerm.{ it; loc; ty } =
      match it with
      | ScopedTerm.Var (v, args) -> (
          to_print (fun () -> Format.eprintf "The env is %a and the var is %a@." pp_env () F.pp v);
          match Env.get !env v with
          | Some e -> Some e
          | None ->
              let ty = Compilation.TypeAssignment.build_app_ty ty args in
              to_print (fun () ->
                  Format.eprintf "Getting functionality from tm @[%a@] tya \n@[%a@] is @[%a@]@." ScopedTerm.pretty_ it
                    (MutableOnce.pp TypeAssignment.pp) ty pp_functionality
                    (Compilation.TypeAssignment.type_ass_2func ~loc global ty));
              Some (Compilation.TypeAssignment.type_ass_2func ~loc global ty))
      | Const (Global { decl_id }, _) ->
          Some
            (match get_functionality ~uf ~loc ~tyag:(ty, []) ~env:global decl_id with
            | Relational -> Functional
            | e -> e)
      | App (Global { decl_id }, _, x, xs) -> Some (get_functionality ~uf ~loc ~tyag:(ty, x :: xs) ~env:global decl_id)
      | App (Bound scope, f, _, _) | Const (Bound scope, f) -> Ctx.get ctx (f, scope)
      | CData _ -> Some (NoProp [])
      | Spill _ -> error ~loc "get_funct_of_term of spilling: "
      | e -> error ~loc (Format.asprintf "get_funct_of_term %a" ScopedTerm.pp_t_ e)
    in

    let rec get_right_most = function Arrow (_, _, r) -> get_right_most r | e -> e in

    let get_func_hd ctx t = Option.value ~default:Any (get_funct_of_term ctx t) |> get_right_most in

    (* let functionality_beta f args ctx =
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
       in *)

    (* the only where the functionality of a term is not known are:
       - Variables
       - Application with unkown variables
       - Lambdas with underlying Variables or ApplicationsFormat.asprintf "%a" ScopedTerm.pretty e
    *)
    let unify_force ScopedTerm.{ it; loc } f =
      match it with
      | Var (v, []) -> add_env ~loc v ~v:f
      | Var (_v, _args) -> error ~loc (Format.asprintf "Unify force of an applied variable %a" ScopedTerm.pretty_ it)
      (* | App () *)
      | _ -> error ~loc "unify_force TODO"
    in

    (* TODO: improve *)
    let functionality_unify ~loc f1 f2 = cmp ~loc f1 f2 = 0 in

    let unify_func ({ loc } as t1 : ScopedTerm.t) (t2 : ScopedTerm.t) f1 f2 : unit =
      match (t1.it, t2.it) with
      | Var _, Var _ -> (
          match (f1, f2) with
          | Any, Any -> ()
          | Any, _ -> unify_force t1 f2
          | _, Any -> unify_force t2 f1
          | _, _ ->
              if not (functionality_unify ~loc f1 f2) then
                error ~loc
                  (Format.asprintf "Functionality of %a is %a and of %a is %a: they do not unify" ScopedTerm.pretty t1
                     pp_functionality f1 ScopedTerm.pretty t2 pp_functionality f2))
      | Var _, _ -> unify_force t1 f2
      | _, Var _ -> unify_force t2 f1
      | _, _ ->
          if not (functionality_unify ~loc f1 f2) then
            error ~loc
              (Format.asprintf "Functionality of %a is %a and of %a is %a: they do not unify" ScopedTerm.pretty t1
                 pp_functionality f1 ScopedTerm.pretty t2 pp_functionality f2)
      (* if ScopedTerm.is_var t1.it && not (ScopedTerm.is_var t2.it) then
           unify_force t1 f2
         else if
         match (f1, f2) with
         | x, y when x = y -> ()
         | (Any | BoundVar _), x -> unify_force t1 f2
         | x, (Any | BoundVar _) -> unify_force t2 f1
         | _, _ ->
             error ~loc:t1.loc
               (Format.asprintf "Cannot unify functionality of %a with %a at %a, their functionalities are\n 1: %a\n 2: %a"
                  ScopedTerm.pretty t1 ScopedTerm.pretty t2 Loc.pp t2.loc pp_functionality f1 pp_functionality f2) *)
    in

    (* let rec unify_func (t1 : ScopedTerm.t_) (t2 : ScopedTerm.t_) (ctx : Ctx.t) : unit =
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
         | Var (vname, args), CData _ -> add_env vname ~v:(NoProp [])
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
               (Format.asprintf "trying to unify \n- %a and \n- %a in \n %a and ctx %a@." ScopedTerm.pp_t_ t1
                  ScopedTerm.pp_t_ t2 pp_env () pp_ctx ctx)
       in *)
    let subst_constructor ~loc f l full_constr =
      let bvars = List.map (function BoundVar n -> n | _ -> assert false) l in
      to_print (fun () ->
          Format.eprintf "Going to subst f:[%a] with l:[%a]" (pplist pp_functionality ",") f (pplist F.pp ",") bvars);
      let add acc bvar f =
        match F.Map.find_opt bvar acc with
        | None -> F.Map.add bvar (F f) acc
        | Some e ->
            assert (e = F f);
            acc
      in
      let map = List.fold_left2 add F.Map.empty bvars f in
      subst ~loc map full_constr
    in

    (* get mode of a constant. if cannot find it, then deduce all output from the functionality
       Like type, functionality informs about the number of arg of the constant.
       In tandem with func2mode we build the mode of the constant wrt the number
       of it Arrows
    *)
    (* let get_mode_func ~loc n f = try get_mode ~loc n with _ -> func2mode f in *)

    let rec all_vars2any ScopedTerm.{ it; loc } =
      match it with
      | ScopedTerm.Var (n, []) -> add_env ~loc n ~v:Any
      | ScopedTerm.Var (n, _) -> failwith "TODO"
      | App (_, _, x, xs) -> List.iter all_vars2any (x :: xs)
      | Impl (_, l, r) -> List.iter all_vars2any [ l; r ]
      | Spill (t, _) -> all_vars2any t
      | Lam (_, _, _, t) -> all_vars2any t
      | Discard | Const (_, _) | CData _ | Cast (_, _) -> ()
      (* | _-> failwith "TODO" *)
    in

    let rec infer_app n ctx t args =
      to_print (fun () -> Format.eprintf "The global app is %a@." F.pp n);
      match get_funct_of_term ctx t with
      | None -> failwith "TODO12"
      | Some AssumedFunctional -> Functional
      | Some e ->
          (* let modes = get_mode_func ~loc:t.loc n e in *)

          to_print (fun () ->
              Format.eprintf "Valid_call with functionality:%a, arg:[%a]@." pp_functionality e
                (pplist ScopedTerm.pretty ",") args);

          let valid_call = valid_call ctx e args in

          to_print (fun () -> Format.eprintf "Valid call for %a is %a@." F.pp n pp_functionality valid_call);

          if valid_call <> Any then (
            let res = infer_outputs ctx e args in
            to_print (fun () -> Format.eprintf "The inferred output is %a@." pp_functionality res);
            res)
          else (
            infer_outputs_fail ctx e args |> ignore;
            Any)
    (* returns Any if the call is not valid *)
    and valid_call ctx =
      fold_on_modes
        (fun e l r ->
          let inferred = infer ctx e in
          if (inferred <<= l) ~loc:e.loc then r else Any)
        (fun _ _ r -> r)
    and infer_outputs ctx =
      fold_on_modes
        (fun _ _ r -> r)
        (fun t l r ->
          to_print (fun () ->
              Format.eprintf "Inferring output %a with func %a@." ScopedTerm.pretty t pp_functionality l);
          match t.ScopedTerm.it with
          | Var (n, []) ->
              add_env ~loc:t.loc n ~v:l;
              r
          | Var (n, args) ->
              let v = get_funct_of_term ctx t |> Option.get in
              add_env ~loc:t.loc n ~v;
              r
          | _ -> if (infer ctx t <<= l) ~loc:t.loc then r else Any)
    and infer_outputs_fail ctx =
      fold_on_modes
        (fun _ _ r -> r)
        (fun t _ r ->
          all_vars2any t;
          r)
    and infer ctx ({ it; loc } as t : ScopedTerm.t) : functionality =
      match it with
      | ScopedTerm.Const _ | CData _ -> get_funct_of_term ctx t |> Option.get
      | Discard -> Functional
      | Var (n, []) -> ( match Env.get !env n with None -> Any | Some e -> e)
      | Var (n, args) -> infer_app n ctx t args
      | Lam (None, _, _type, t) -> arr Output (Compilation.TypeAssignment.type_ass_2func ~loc global _type) (infer ctx t)
      | Lam (Some vname, _, _type, t) ->
          let v = Compilation.TypeAssignment.type_ass_2func ~loc global _type in
          to_print (fun () ->
              Format.eprintf "Going under lambda %a with func: %a@." F.pp (fst vname) pp_functionality v);
          arr Output v (infer (add_ctx ~loc ctx vname ~v) t)
      | Impl (true, _hd, t) -> infer ctx t (* TODO: hd is ignored *)
      | Impl (false, _, t) -> infer ctx t (* TODO: this is ignored *)
      | App (Global _, n, x, [ y ]) when F.equal F.eqf n || F.equal F.isf n || F.equal F.asf n ->
          to_print (fun () ->
              Format.eprintf "Calling inference for unification between \n - (@[%a@])\n - (@[%a@])@." ScopedTerm.pretty
                x ScopedTerm.pretty y);
          let f1, f2 = (infer ctx x, infer ctx y) in
          to_print (fun () -> Format.eprintf "Inferred are \n - %a\n -%a@." pp_functionality f1 pp_functionality f2);
          unify_func x y f1 f2;
          Functional
      | App (Global _, n, x, xs) when F.equal F.andf n ->
          let args = x :: xs in
          List.fold_left (fun acc e -> infer ctx e |> max ~loc:e.ScopedTerm.loc acc) Functional args
      | App (Global _, n, x, []) when F.equal F.pif n || F.equal F.sigmaf n -> (
          match infer ctx x with
          | Arrow (_, _, r) -> r
          | e -> error ~loc (Format.asprintf "Type error (%a is not a function)" ScopedTerm.pretty_ it))
      | App (_, n, x, xs) -> (
          match get_funct_of_term ctx t with
          | None -> error ~loc "TODO22" (* TODO: The functionality of t is not known... should be taken into account *)
          | Some e -> infer_app n ctx t (x :: xs))
      | Cast (t, _) -> infer ctx t
      | Spill (a, { contents = Main spill_nb }) ->
          let func = infer ctx a in

          (* All spilled vars should be leq of  *)
          error ~loc (Format.asprintf "Spilled %i func is %a" spill_nb pp_functionality func)
      | Spill _ -> error ~loc "Spill with no known nb of spilled variables: should be known after typechecking"
    in

    let check_head_input =
      let rec build_hyps_head_aux ctx = function
        | [], _ -> ()
        | (it : ScopedTerm.t) :: tl, Arrow (_, l, r) ->
            build_hyp_head ctx l it;
            build_hyps_head_aux ctx (tl, r)
        | x :: xs, NoProp (f :: fs) ->
            build_hyp_head ctx f x;
            build_hyps_head_aux ctx (xs, NoProp fs)
        | { loc } :: _, _ -> anomaly ~loc "Type error5"
      and build_hyp_head (ctx : Ctx.t) (assumed : functionality) ({ loc; it } as t : ScopedTerm.t) =
        match it with
        | ScopedTerm.Const _ | Discard | CData _ -> ()
        | Var (n, _args) -> add_env ~loc n ~v:assumed
        | Lam (None, _, _type, t) -> build_hyp_head ctx (eat_abs ~loc assumed |> snd) t
        | Lam (Some x, _, _type, t) ->
            let v, assumed = eat_abs ~loc assumed in
            build_hyp_head (add_ctx ~loc ctx x ~v) assumed t (* TODO: Here I use any instead of Relational ...*)
        | Impl (true, _hd, t) -> () (* TODO: this is ignored *)
        | Impl (false, _, _) -> () (* TODO: this is ignored *)
        | App (Global _, n, x, [ y ]) when F.equal F.isf n || F.equal F.eqf n || F.equal F.asf n ->
            build_hyp_head ctx assumed x;
            build_hyp_head ctx assumed y;
            let f1 = infer ctx x in
            let f2 = infer ctx y in
            if cmp f1 f2 ~loc <> 0 then
              error ~loc:x.loc
                (Format.asprintf "Unification with two different functionalities: \n %a : %a and \n %a : %a"
                   ScopedTerm.pretty x pp_functionality f1 ScopedTerm.pretty y pp_functionality f2)
        | App (_, n, x, xs) -> (
            to_print (fun () ->
                Format.eprintf ".The global app is %a and its functionality is %a@." F.pp n
                  (Format.pp_print_option pp_functionality)
                  (get_funct_of_term ctx t));
            match get_funct_of_term ctx t with
            | None -> () (* TODO: The functionality of t is not already known... should be taken into account *)
            | Some e -> (
                let rm = get_right_most e in
                match (rm, assumed) with
                | NoProp l, NoProp l1 ->
                    (* We want to map each bound variable in the functionality of the found term with the assumed *)
                    (* For example:
                       pred p i:(pr (pred o:int) int).
                       p (pr X Y) :- X Y.

                       While analyzing p.
                       The assumed functionality of its first argument is `ass: NoProp[NoProp -> Relational, NoProp]`.
                       The functionality of the constructor `|` is `fc: A -> B -> pair A B`
                       We recursively replace in `fc` the bound variable appearing in its conclusion (i.e `[A,B]`)
                       with the list of functionality in `ass`.
                       This gives `fc: (NoProp -> Relational) -> NoProp -> NoProp`
                       This way, build_hyps_head_aux will set the functionality of `X` to `NoProp -> Relational`
                       and `Y` to `NoProp`.
                       This way the call `X Y` is meaningful
                    *)
                    to_print (fun () ->
                        Format.eprintf "In noProp branch with term: %a and func %a@." ScopedTerm.pretty t
                          pp_functionality assumed);
                    let f1 = subst_constructor ~loc l1 l e in
                    to_print (fun () -> Format.eprintf "The subst constructor is %a@." pp_functionality f1);
                    (* failwith "STOP" |> ignore; *)
                    build_hyps_head_aux ctx (x :: xs, f1)
                | _, _ -> (
                    match e with
                    | Any | BoundVar _ | AssumedFunctional ->
                        build_hyps_head_aux ctx (x :: xs, List.fold_right (fun _ acc -> arr Output Any acc) (x :: xs) Any)
                    | Arrow _ -> build_hyps_head_aux ctx (x :: xs, e)
                    | Functional | Relational | NoProp _ ->
                        error ~loc (Format.asprintf "Unexpected %a for %a" pp_functionality assumed ScopedTerm.pretty t)
                    )))
        | Cast (t, _) -> build_hyp_head ctx assumed t
        | Spill _ -> error ~loc "Spill in the head"
      and build_hyps_head_modes ctx =
        fold_on_modes
          (fun arg l r ->
            build_hyp_head ctx l arg;
            r)
          (fun arg l r -> r)
      and build_hyps_head (ctx : Ctx.t) ({ it; loc } as t : ScopedTerm.t) =
        match it with
        | ScopedTerm.Const _ -> ()
        | App (Global { decl_id }, f, x, xs) -> (
            match get_funct_of_term ctx t with
            | None -> assert false (* TODO: The functionality is not know... *)
            | Some e ->
                to_print (fun () ->
                    Format.eprintf "Before call to build_hyps_head_modes, func of %a is %a@." F.pp f pp_functionality e);
                build_hyps_head_modes ctx e (x :: xs) |> ignore)
        | App (Bound _, f, _, _) -> error ~loc (Format.asprintf "No signature for predicate %a@." F.pp f)
        | Var _ -> error ~loc "Flex term used has head of a clause"
        | _ -> error ~loc (Format.asprintf "Build_hyps_head: type error, found %a" ScopedTerm.pp t)
      in
      build_hyps_head
    in

    let check_body ctx tm exp : unit =
      let check ctx (t : ScopedTerm.t) (exp : functionality) : unit =
        let before, after = split_bang t in

        List.iter (fun e -> infer ctx e |> ignore) before;

        List.iter
          (fun e ->
            to_print (fun () -> Format.eprintf "Check premise @[%a@] in env @[%a@]@." ScopedTerm.pretty e pp_env ());
            let inferred = infer ctx e in
            to_print (fun () ->
                Format.eprintf "Checking inferred is %a and expected is %a of @[%a@]@." pp_functionality inferred
                  pp_functionality exp ScopedTerm.pretty e);
            functionality_leq_error ~pref:(Format.asprintf "%a" ScopedTerm.pretty e) ~loc:e.ScopedTerm.loc inferred exp)
          after
      in

      check ctx tm exp
    in

    let check_head_output =
      let build_hyps_head_modes ctx =
        fold_on_modes
          (fun _ _ -> Fun.id)
          (fun arg l ->
            functionality_leq_error ~pref:(Format.asprintf "%a" ScopedTerm.pretty arg) ~loc:arg.loc (infer ctx arg) l;
            Fun.id)
      in
      let build_hyps_head (ctx : Ctx.t) ({ it; loc } as t : ScopedTerm.t) =
        match it with
        | ScopedTerm.Const _ -> ()
        | App (Global { decl_id }, f, x, xs) -> (
            match get_funct_of_term ctx t with
            | None -> assert false (* TODO: The functionality is not know... *)
            | Some e -> build_hyps_head_modes ctx e (x :: xs) |> ignore)
        | App (Bound _, f, _, _) -> error ~loc (Format.asprintf "No signature for predicate %a@." F.pp f)
        | Var _ -> error ~loc "Flex term used has head of a clause"
        | _ -> error ~loc "type error7"
      in
      build_hyps_head
    in

    let main ctx ({ it; loc } as tm : ScopedTerm.t) : unit =
      let hd, body =
        match it with
        | App _ | Const _ -> (tm, None)
        | Impl (false, ({ it = Const _ } as t), _) ->
            (t, None) (* Clauses with no argument heads are no checked, i.e.: empty body *)
        | Impl (false, hd, body) -> (hd, Some body)
        | Var _ -> failwith "flexible clause..."
        | _ -> failwith "Type error8"
      in
      to_print (fun () ->
          Format.eprintf "=====================================================@.";
          Format.eprintf "The head is `%a`@." ScopedTerm.pretty hd);
      check_head_input ctx hd;
      to_print (fun () -> Format.eprintf "END HEAD CHECK@.");

      to_print (fun () -> Format.eprintf "The contex_head is %a@." pp_env ());

      (* Format.eprintf "Getting the functionality of %a and func hd is %a@." ScopedTerm.pp hd pp_functionality (get_func_hd ctx hd); *)
      Option.iter (fun body -> check_body ctx body (get_func_hd ctx hd)) body;

      if body <> None then check_head_output ctx hd
      (* if F.equal (F.from_string "map-ok") (get_namef hd) then failwith "STOP" *)
    in
    main Ctx.empty tm;
    to_print (fun () -> Format.eprintf "The env is %a@." pp_env ())
end

let to_check_clause ScopedTerm.{ it; loc } =
  let n = get_namef it in
  not (F.equal n F.mainf)
(* && Re.Str.string_match (Re.Str.regexp ".*test.*") (Loc.show loc) 0 *)
&& Re.Str.string_match (Re.Str.regexp ".*test.*functionality.*") (Loc.show loc) 0

let check_clause ?uf ~loc ~env t =
  if to_check_clause t then (
    to_print (fun () ->
        (* check_clause ~loc ~env F.Map.empty t |> ignore *)
        Format.eprintf "============== STARTING mode checking %a@." Loc.pp t.loc
        (* Format.eprintf "Modes are [%a]" (F.Map.pp (fun fmt ((e:mode_aux list),_) -> Format.fprintf fmt "%a" pp_mode e)) (modes); *)
        (* Format.eprintf "Functional preds are %a@." pp env; *));
    Checker_clause.check ?uf ~global:env t)

class merger (all_func : env) =
  object (self)
    val mutable all_func = all_func
    val mutable local_func = empty_fmap

    method private add_func is_ty_abbr id ty =
      let loc, func = Compilation.ScopeTE.type2func all_func ty in
      let n = ty.name in
      (* Format.eprintf "Adding constant %a with id %i\n%!" F.pp n id; *)
      if is_ty_abbr then all_func <- Compilation.add_type ~loc is_ty_abbr ~id ~n all_func func;
      local_func <- Compilation.add_type ~loc is_ty_abbr ~id ~n local_func func

    method get_all_func = all_func
    method get_local_func = local_func
    method add_ty_abbr = self#add_func true
    method add_func_ty_list ty id_list = List.iter2 (self#add_func false) id_list ty
    method merge : env = merge all_func local_func
  end

(* module Test = struct
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
   end *)
