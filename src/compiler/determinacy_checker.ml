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

(* TYPE DECLARATION FOR FUNCTIONALITY *)

type f = 
  | Functional of f list  (* Used for functional preds, the f list represents the functionality relation of the arguments *)
  | Relational of f list  (* Used for non-functional preds, the f list represents the functionality relation of the arguments *)
  | NoProp                (* Used for kinds like list, int, string... and abstractions not being props like: (int -> list bool), (string -> nat -> string) *)
  | AssumedFunctional     (* Currently used for variadic functions, like print, halt... *)
  | BoundVar of F.t
[@@ deriving show, ord]

type t' = Lam of F.t * t' | F of f [@@ deriving show, ord]
type t = Loc.t * t' [@@ deriving show, ord]

type func_map = {
  ty_abbr: Scope.type_decl_id F.Map.t; (* Invariant every type_abbrev const is already in cmap *)
  cmap: (F.t * t) C.Map.t
} [@@ deriving show, ord]

type fname = F.t * t [@@deriving show,ord]

let pp_locs fmt (l: t list) =
  Format.fprintf fmt "[%a]" (pplist (fun fmt -> Format.fprintf fmt "%a" Loc.pp) ",") (List.map fst l)

let compare_t (a:t) (b:t) = compare_t' (snd a) (snd b)

let compare_fname a b = compare_t (snd a) (snd b)

let mk_func_map ty_abbr cmap = {ty_abbr; cmap}

let empty_fmap = {ty_abbr = F.Map.empty; cmap = C.Map.empty}

let get_functionality_tabbr_opt map k = match F.Map.find_opt k map.ty_abbr with
  None -> None | Some e -> Some (C.Map.find e map.cmap)

let get_functionality map k = C.Map.find k map.cmap

(* AUXILIARY FUNCTIONS *)
let rec subst ~loc sigma : f -> f = function
  | BoundVar k as t ->
    begin match F.Map.find_opt k sigma with
    | None -> t
    | Some (F f) -> f
    | Some (Lam (_,b)) -> error ~loc "type_abbrev not fully applied"
    end
  | Functional l -> Functional (List.map (subst ~loc sigma) l)
  | AssumedFunctional | Relational _ | NoProp as t -> t

let rec bind ~loc sigma : (t'*f list) -> f = function
  | Lam (n,b), x::xs -> bind ~loc (F.Map.add n (F x) sigma) (b,xs)
  | Lam (_,b), [] -> error ~loc "type_abbrev is not fully applied"
  | F t, [] -> subst ~loc sigma t
  | F _, _::_ -> anomaly ~loc "type_abbrev is too much applied"

(* COMPILATION from SCOPE_TYPE_EXPRESSION TO FUNCTIONALITY *)
module Compilation = struct
  let add_type is_type_abbr fmap ~n ~id v = 
    if is_type_abbr && F.Map.mem n fmap.ty_abbr then
      error (Format.asprintf "Adding again type_abbrev %a" F.pp n);
    let cmap = C.Map.add id (n,v) fmap.cmap in
    let ty_abbr = if is_type_abbr then F.Map.add n id fmap.ty_abbr else fmap.ty_abbr in
    mk_func_map ty_abbr cmap

  let merge f1 f2 = 
    let union_same pk pe cmpe k e1 e2 = 
      (* if cmpe e1 e2 = 0 then  *)
        Some e1
      (* else error (Format.asprintf "The key %a has two different values (v1:%a) (v2:%a)" pk k pe e1 pe e2)  *)
    in
    let cmap = C.Map.union (union_same pp_int pp_fname compare_fname) f1.cmap f2.cmap in
    let ty_abbr = F.Map.union (union_same F.pp pp_int Int.compare) f1.ty_abbr f2.ty_abbr in
    mk_func_map ty_abbr cmap

  let map_snd f = List.map (fun (_, ScopedTypeExpression.{it}) -> f it)

  let rec type2func_ty_abbr ~loc bound_vars (fmap: func_map) c args =
    match get_functionality_tabbr_opt fmap c with
    | None -> NoProp        (* -> c is a kind (like list, int, ...) *) 
    | Some (_,f) ->         (* -> c is a type-abbrev *)
      bind ~loc F.Map.empty (snd f, List.map (type2func_loc ~loc bound_vars fmap) args) 

  and type2func ~loc bound_vars (fmap: func_map) : ScopedTypeExpression.t_ -> f = function
    | Pred(Function, xs) -> Functional (map_snd (type2func ~loc bound_vars fmap) xs)
    | Pred(Relation, xs) -> Relational (map_snd (type2func ~loc bound_vars fmap) xs)
    | Const (_,c) when F.Set.mem c bound_vars -> BoundVar c
    | Const (_,c) -> type2func_ty_abbr ~loc bound_vars fmap c []
    | App(c,x,xs) -> type2func_ty_abbr ~loc bound_vars fmap c (x::xs)
    | Arrow (Variadic, _, _) -> AssumedFunctional
    (* Invariant: the rightmost type in the right branch is not a prop due flatten_arrows in compiler *)
    | Arrow (NotVariadic,_,_) -> NoProp
    | Any -> NoProp
  and type2func_loc ~loc bvars fmap ScopedTypeExpression.{it} = type2func ~loc bvars fmap it

  let rec type2func_lam bound_vars type_abbrevs : ScopedTypeExpression.v_ -> t = function
    | Lam (n, t) -> 
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
  | AssumedFunctional, t -> error (Format.asprintf "Cannot compare %a with %a" pp_f a pp_f b) (* TODO: print could be passed in a functional position *)
  | _, AssumedFunctional -> error (Format.asprintf "Cannot compare %a with %a" pp_f a pp_f b)
  | Relational xs, Relational ys -> functionalities_leq xs ys
  | _, Relational _ -> true
  | Relational _, _ -> false
  | Functional xs, Functional ys -> functionalities_leq xs ys
  | BoundVar _, _ | _, BoundVar _ -> true (* TODO: this is not correct... *)
  | NoProp, NoProp -> true
  | NoProp, _ | _, NoProp -> error "Type error, expected noProp found predicate"

let functionality_leq_err ~loc c f' f =
  if not (functionality_leq f' f) then
    error ~loc (Format.asprintf "Functionality of %a is %a and is not included in %a" F.pp c pp_f f' pp_f f)

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

let rec head_ag_func_pairing functional_preds args fs = 
  let func_vars = ref F.Map.empty in
  let rec aux ~loc f = function
    | ScopedTerm.Const (Global _,c) -> (* Look into type_abbrev for global symbols *)
      (* Format.eprintf "1Looking for the constant %a\n%!" F.pp c; *)
      begin match get_functionality_bvars functional_preds c with
      | (f') -> functionality_leq_err ~loc c f' f
      (* | Lam _ -> failwith "Error not fully applied" *)
      end
    | Const _ -> failwith "TODO"
    | App(_,hd,x,xs) -> 
      Format.eprintf "2Looking for the constant %a -- %a\n%!" F.pp hd (pplist ScopedTerm.pp ",") (x::xs);
      let f' = get_functionality_bvars functional_preds hd in
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

and check_head functional_preds func_vars head_name head_args =
  match get_functionality_bvars functional_preds head_name with
  | NoProp -> raise StopCheck
  | AssumedFunctional -> raise StopCheck
  | Functional l | Relational l -> head_ag_func_pairing functional_preds head_args l
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

let check_clause ~loc ~functional_preds t =
  check_clause ~loc ~functional_preds F.Map.empty t |> ignore

class merger (all_func: func_map) = object(self)
  val mutable all_func = all_func
  val mutable local_func = empty_fmap

  method private add_func is_ty_abbr n id ty =
    let func = Compilation.type2func all_func ty in
    if is_ty_abbr then all_func <- Compilation.add_type is_ty_abbr ~id ~n all_func func;
    local_func <- Compilation.add_type is_ty_abbr ~id ~n local_func func;

  method get_all_func = all_func
  method get_local_func = local_func

  method add_ty_abbr = self#add_func true

  method add_func_ty_list name ty (ty_w_id : TypeAssignment.overloaded_skema_with_id) = 
    let id_list = match ty_w_id with Single e -> [fst e] | Overloaded l -> List.map fst l in
    List.iter2 (self#add_func false name) id_list ty

end