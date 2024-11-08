(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Elpi_util
open Util
open Elpi_parser
open Ast
open Compiler_data

module C = Constants

exception StopCheck

let to_print f = if false then f () 

(* TYPE DECLARATION FOR FUNCTIONALITY *)

type 'a functionality = 
  | Functional of 'a functionality list  (* Used for functional preds, the f list represents the functionality relation of the arguments *)
  | Relational of 'a functionality list  (* Used for non-functional preds, the f list represents the functionality relation of the arguments *)
  | NoProp                (* Used for kinds like list, int, string... and abstractions not being props like: (int -> list bool), (string -> nat -> string) *)
  | AssumedFunctional     (* Currently used for variadic functions, like print, halt... *)
  | BoundVar of 'a
[@@ deriving show, ord]

type 'a functionality_abs = Lam of F.t * 'a functionality_abs | F of 'a functionality [@@ deriving show, ord]
type 'a functionality_loc = Loc.t * 'a functionality_abs [@@ deriving show, ord]

type t = {
  ty_abbr: Scope.type_decl_id F.Map.t; (* Invariant every type_abbrev const is already in cmap *)
  cmap: (F.t * F.t functionality_loc) C.Map.t
} [@@ deriving show, ord]

type env = t (* This is for the module signature *)

let compare_functionality_loc cmp a b = compare_functionality_abs cmp (snd a) (snd b)

let compare_fname a b = compare_functionality_loc (snd a) (snd b)

let mk_func_map ty_abbr cmap = {ty_abbr; cmap}

let empty_fmap = {ty_abbr = F.Map.empty; cmap = C.Map.empty}

let get_functionality_tabbr_opt map k = match F.Map.find_opt k map.ty_abbr with
  None -> None | Some e -> Some (C.Map.find e map.cmap)

let get_functionality ~loc ~env k = 
  if k = 0 then F NoProp else (* k = 0 is for polymorphic types marked with any *)
  try C.Map.find k env.cmap |> snd |> snd 
  with e -> Format.eprintf "Error at %a with const %i\n%!" Loc.pp loc k; raise e

(* AUXILIARY FUNCTIONS *)
let rec subst ~loc sigma = function
  | BoundVar k as t ->
    begin match F.Map.find_opt k sigma with
    | None -> t
    | Some (F f) -> f
    | Some (Lam (_,b)) -> error ~loc "type_abbrev not fully applied"
    end
  | Functional l -> Functional (List.map (subst ~loc sigma) l)
  | AssumedFunctional | Relational _ | NoProp as t -> t

let rec bind ~loc sigma = function
  | Lam (n,b), x::xs -> bind ~loc (F.Map.add n (F x) sigma) (b,xs)
  | Lam (_,b), [] -> error ~loc "type_abbrev is not fully applied"
  | F t, [] -> subst ~loc sigma t
  | F _, _::_ -> anomaly ~loc "type_abbrev is too much applied"

let bind = bind F.Map.empty

let rec partial_bind ~loc sigma = function
  | Lam (n,b), x::xs -> partial_bind ~loc (F.Map.add n (F x) sigma) (b,xs)
  | Lam (n,b), [] -> Lam (n, partial_bind ~loc sigma (b, []))
  | F t, [] -> F (subst ~loc sigma t)
  | F _, _::_ -> anomaly ~loc "type_abbrev is too much applied"
let partial_bind = partial_bind F.Map.empty

(* COMPILATION from SCOPE_TYPE_EXPRESSION TO FUNCTIONALITY *)
module Compilation = struct
  let add_type is_type_abbr env ~n ~id v = 
    if is_type_abbr && F.Map.mem n env.ty_abbr then
      error (Format.asprintf "Adding again type_abbrev %a" F.pp n);
    let cmap = C.Map.add id (n,v) env.cmap in
    let ty_abbr = if is_type_abbr then F.Map.add n id env.ty_abbr else env.ty_abbr in
    mk_func_map ty_abbr cmap

  let merge f1 f2 = 
    let pp_fname fmt (x,y) = Format.fprintf fmt "(%a,%a)" F.pp x (pp_functionality_loc F.pp) y in
    let compare_fname (x0,y0) (x1,y1) = 
      let cmp = F.compare x0 x1 in
      if cmp = 0 then (compare_functionality_loc F.compare) y0 y1 else cmp
    in
    let union_same pk pe cmpe k e1 e2 =
      (* if cmpe e1 e2 = 0 then  *)
        Some e1
      (* else error (Format.asprintf "The key %a has two different values (v1:%a) (v2:%a)" pk k pe e1 pe e2)  *)
    in
    let cmap = C.Map.union (union_same pp_int pp_fname compare_fname) f1.cmap f2.cmap in
    let ty_abbr = F.Map.union (union_same F.pp pp_int Int.compare) f1.ty_abbr f2.ty_abbr in
    mk_func_map ty_abbr cmap

  let map_snd f = List.map (fun (_, ScopedTypeExpression.{it}) -> f it)

  let rec type2func_ty_abbr ~loc bound_vars (env: env) c args =
    match get_functionality_tabbr_opt env c with
    | None -> NoProp        (* -> c is a kind (like list, int, ...) *) 
    | Some (_,f) ->         (* -> c is a type-abbrev *)
      bind ~loc (snd f, List.map (type2func_loc ~loc bound_vars env) args) 

  and type2func ~loc bound_vars (env: env) = function
    | ScopedTypeExpression.Pred(Function, xs) -> Functional (map_snd (type2func ~loc bound_vars env) xs)
    | Pred(Relation, xs) -> Relational (map_snd (type2func ~loc bound_vars env) xs)
    | Const (_,c) when F.Set.mem c bound_vars -> BoundVar c
    | Const (_,c) -> type2func_ty_abbr ~loc bound_vars env c []
    | App(c,x,xs) -> type2func_ty_abbr ~loc bound_vars env c (x::xs)
    | Arrow (Variadic, _, _) -> AssumedFunctional
    (* Invariant: the rightmost type in the right branch is not a prop due flatten_arrows in compiler *)
    | Arrow (NotVariadic,_,_) -> NoProp
    | Any -> NoProp
  and type2func_loc ~loc bvars env ScopedTypeExpression.{it} = type2func ~loc bvars env it

  let rec type2func_lam bound_vars type_abbrevs = function
    | ScopedTypeExpression.Lam (n, t) -> 
      let (loc, r) = type2func_lam (F.Set.add n bound_vars) type_abbrevs t in
      loc, Lam (n,r)
    | Ty {it;loc} -> loc, F (type2func ~loc bound_vars type_abbrevs it)

  let type2func f (x:ScopedTypeExpression.t) = type2func_lam F.Set.empty f x.value
end
let merge = Compilation.merge

let rec functionalities_leq l1 l2 = match l1, l2 with
  | _, [] -> true (* l2 can be any length (due to partial application) *)
  | x::xs, y::ys -> functionality_leq x y && functionalities_leq xs ys
  | [], _ -> error "the first list of functional args is can't been smaller then the second one: type error"

and functionality_leq a b = match a, b with
  | AssumedFunctional, AssumedFunctional -> true
  | AssumedFunctional, t -> error (Format.asprintf "Cannot compare %a with %a" (pp_functionality F.pp) a (pp_functionality F.pp) b) (* TODO: print could be passed in a functional position *)
  | _, AssumedFunctional -> error (Format.asprintf "Cannot compare %a with %a" (pp_functionality F.pp) a (pp_functionality F.pp) b)
  | Relational xs, Relational ys -> functionalities_leq xs ys
  | _, Relational _ -> true
  | Relational _, _ -> false
  | Functional xs, Functional ys -> functionalities_leq xs ys
  | BoundVar _, _ | _, BoundVar _ -> true (* TODO: this is not correct... *)
  | NoProp, NoProp -> true
  | NoProp, _ | _, NoProp -> error "Type error, expected noProp found predicate"

let functionality_leq_err ~loc c f' f =
  if not (functionality_leq f' f) then
    error ~loc (Format.asprintf "Functionality of %a is %a and is not included in %a" F.pp c (pp_functionality F.pp) f' (pp_functionality F.pp) f)

let rec eat_lambdas = function
  | Lam (_,b) -> eat_lambdas b
  | F b -> b

let get_functionality_bvars map k = 
  F.Map.find k map |> eat_lambdas

(* 
  Invariant every constant in the map is functional:
  i.e. for each k in the domain, map[k] = Functional [...]
*)
let is_functional map k = match get_functionality_bvars map k with
  | Functional _ | NoProp | AssumedFunctional -> true
  | Relational _ | BoundVar _ -> false

module Checker = struct

  module Ctx : sig
    (** Used for global variables unification variables, it associates to
        each variable name its functionality *)
    type t = F.t functionality_abs [@@deriving show]
    type ctx [@@deriving show]
    val empty : ctx
    val add : ctx -> F.t -> t -> ctx
    val get : ctx -> F.t -> t
  end = struct
    type t = F.t functionality_abs [@@deriving show]
    type ctx = t F.Map.t [@@deriving show]
    let empty = F.Map.empty
    let add (ctx:ctx) k v = 
      match F.Map.find_opt k ctx with
      | None -> F.Map.add k v ctx
      | Some v' ->
        if compare_functionality_abs F.compare v v' <= 0 then F.Map.add k v ctx
        else ctx

    let get ctx k = F.Map.find k ctx
  end
  
  let forceF ~loc = function F x -> x | _ -> error ~loc "Cannot force F"

  let rec get_funct_of_term_loc ~loc bvars ~ctx ~env ({it}: ScopedTerm.t) =
    get_funct_of_term ~loc bvars ~ctx ~env it 
  and get_funct_of_term ~loc bvars ~ctx ~(env: env) (t: ScopedTerm.t_) = match t with
    | App(Global {decl_id},f,x,xs) -> get_functionality ~loc ~env decl_id
    | App(Bound _,f,x,xs) -> F.Map.find f bvars
    | Const (Global {decl_id}, _) -> get_functionality ~loc ~env decl_id
    | e -> error ~loc (Format.asprintf "get_func of term %a" ScopedTerm.pp_t_ e)

  let rec check_head_list ~bvars ~ctx ~loc ~env = function
    | [], _ -> ctx
    | ScopedTerm.{it} :: tl, f :: fs ->
      check_head_list ~bvars ~ctx:(check_head ~bvars ~ctx ~loc ~env it (F f)) ~loc ~env (tl, fs)
    | _ :: _, [] -> anomaly "Type error"

  (* Assigns to each variable encountered its functionality *)
  and check_head ~bvars ~ctx ~loc ~env (t: ScopedTerm.t_) f =
    match t with
    | CData _ | Discard | Const _ -> ctx
    | Impl _ -> check_clause ~ctx ~loc ~env t
    | Cast ({it},_) -> check_head ~bvars ~ctx ~loc ~env it f
    | Var (n, (*TODO:*)_) -> Ctx.add ctx n f
    | Lam (None, _ty, {it}) -> check_head ~bvars ~(ctx:Ctx.ctx) ~loc ~env t f

    | Lam (Some(n,_),_,{it}) ->
      begin match forceF ~loc f with
      (* the type is like (A -> ... -> B) where B is not a prop *)
      | NoProp -> ctx
      (* the type is like (A -> ... -> p) where B is a prop *)
      | Functional l | Relational l -> 
        let bvars = F.Map.add n (F (List.hd l)) bvars in 
        check_head ~bvars ~ctx ~loc ~env it (F (Relational (List.tl l)))
      | AssumedFunctional -> check_head ~bvars ~ctx ~loc ~env it f
      | BoundVar _ -> ctx
      end

    | App (Global _,n,x,xs) ->
      to_print (fun () -> Format.eprintf "The global app is %a@." F.pp n);
      begin match get_funct_of_term ~loc bvars ~ctx ~env t |> eat_lambdas with
      | NoProp -> ctx
      | Functional l | Relational l -> check_head_list ~bvars ~ctx ~loc ~env (x::xs, l)
      | AssumedFunctional -> List.fold_right (fun e ctx -> check_head ~bvars ~ctx ~loc ~env e.ScopedTerm.it (F AssumedFunctional)) (x::xs) ctx
      | BoundVar _ -> ctx
      end

    (* TODO: we should have a local set of variables where to put the information about bound vars... *)
    | App (Bound _,n,x,xs) ->
      begin match get_funct_of_term ~loc bvars ~ctx ~env t |> eat_lambdas with
      | NoProp -> ctx
      | Functional l | Relational l -> check_head_list ~bvars ~ctx ~loc ~env (x::xs, l)
      | AssumedFunctional -> List.fold_right (fun e ctx -> check_head ~bvars ~ctx ~loc ~env e.ScopedTerm.it (F AssumedFunctional)) (x::xs) ctx
      | BoundVar _ -> ctx
      end
    | Spill _ -> anomaly "Spill in the head of a clause is forbidden"

  and check_body ~ctx ~loc ~env (t : ScopedTerm.t_) = failwith "TODO"
  
  and check_body_loc ScopedTerm.{it} = check_body it

  and check_clause ~(ctx:Ctx.ctx) ~loc ~env (t: ScopedTerm.t_) =
    match t with
    | App _ | Const _ -> check_head ~bvars:(F.Map.empty) ~ctx ~loc ~env t (F NoProp) (* clauses with no body: they are functional! *)
    | Impl(false, hd, body) -> check_head ~bvars:(F.Map.empty) ~ctx ~loc ~env hd.it (F NoProp)
    | _ -> error ~loc "type error"

  and check_clause_loc ScopedTerm.{it} = check_clause it

  let check_clause ~loc = check_clause_loc ~ctx:Ctx.empty ~loc 
end

module Old = struct
let rec head_ag_func_pairing env args fs = 
  let func_vars = ref F.Map.empty in
  let rec aux ~loc f = function
    | ScopedTerm.Const (Global _,c) -> (* Look into type_abbrev for global symbols *)
      (* Format.eprintf "1Looking for the constant %a\n%!" F.pp c; *)
      begin match get_functionality_bvars env c with
      | (f') -> functionality_leq_err ~loc c f' f
      (* | Lam _ -> failwith "Error not fully applied" *)
      end
    | Const _ -> failwith "TODO"
    | App(_,hd,x,xs) -> 
      (* Format.eprintf "2Looking for the constant %a -- %a\n%!" F.pp hd (pplist ScopedTerm.pp ",") (x::xs); *)
      let f' = get_functionality_bvars env hd in
      (* let f' = bind functional_preds (f', List.map (get_functionality functional_preds) (x::xs)) in *)
      functionality_leq_err ~loc hd f' f;
      begin match f' with
      | Functional l -> aux' (x::xs) l
      | _ -> ()
      end
    | Impl _ -> error "TODO" (* Example p (a => b) *)
    | Discard -> ()
    | Var (v, ag) ->
      begin match F.Map.find_opt v !func_vars with
      | None -> func_vars := F.Map.add v f !func_vars (* -> First appereance of the variable in the head *)
      | Some f' -> functionality_leq_err ~loc v f' f
      end
    | Lam (None, _type, {it}) -> failwith "TODO"
    | Lam (Some (e,_), _type, {it}) -> failwith "TODO"
    | CData _ -> assert (f = NoProp) (* note that this is also true, otherwise we would have a type error *)
    | Spill _ -> error "Spill in the head of a clause forbidden"
    | Cast ({it},_) -> aux ~loc f it
  and aux' args fs = match args, fs with
    | [], [] -> ()
    | ScopedTerm.{it;loc}::xs, y::ys -> aux ~loc y it; aux' xs ys 
    | _ -> failwith "Partial application ??" 
  in
  aux' args fs;
  !func_vars

and check_head env func_vars head_name head_args =
  match get_functionality_bvars env head_name with
  | NoProp -> raise StopCheck
  | AssumedFunctional -> raise StopCheck
  | Functional l | Relational l -> head_ag_func_pairing env head_args l
  | BoundVar v -> error "unreachable branch"

and check_body func_vars = func_vars

let rec check_clause ~loc ~functional_preds func_vars ScopedTerm.{it} =
  match it with
  | Impl(false, hd, body) -> 
    check_clause ~loc ~functional_preds func_vars hd |> check_body
  | App(_,c,x,xs) -> 
    begin
      if String.starts_with ~prefix:"std.map." (F.show c) then func_vars
      else func_vars (* TODO: activate the check by uncommenting the following lines... *)
        (* try check_head functional_preds func_vars c (x::xs)
        with StopCheck -> func_vars  *)
    end
  | Const (_,_) -> func_vars (* a predicate with arity 0 is functional *)
  | _ -> error ~loc "invalid type"
end

let check_clause ~loc ~env t =
  (* check_clause ~loc ~env F.Map.empty t |> ignore *)
  let _ctx = Checker.check_clause ~loc ~env t in
  to_print (fun () -> 
    Format.eprintf "The terms is %a@." ScopedTerm.pp t;
    Format.eprintf "The contex is %a@." Checker.Ctx.pp_ctx _ctx);
  ()

class merger (all_func: env) = object(self)
  val mutable all_func = all_func
  val mutable local_func = empty_fmap

  method private add_func is_ty_abbr n id ty =
    let func = Compilation.type2func all_func ty in
    (* Format.eprintf "Adding constant %a with id %i\n%!" F.pp n id; *)
    if is_ty_abbr then all_func <- Compilation.add_type is_ty_abbr ~id ~n all_func func;
    local_func <- Compilation.add_type is_ty_abbr ~id ~n local_func func;

  method get_all_func = all_func
  method get_local_func = local_func

  method add_ty_abbr = self#add_func true

  method add_func_ty_list name ty (ty_w_id : TypeAssignment.overloaded_skema_with_id) = 
    let id_list = match ty_w_id with Single e -> [fst e] | Overloaded l -> List.map fst l in
    List.iter2 (self#add_func false name) id_list ty

end