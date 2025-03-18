(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Elpi_util.Util
open Elpi_parser.Ast
open Compiler_data
module C = Constants
module UF = IdPos.UF

type dtype =
  | Det  (** -> for deterministic preds *)
  | Rel  (** -> for relational preds *)
  | Exp of dtype list  (** -> for kinds like list, int, string *)
  | BVar of F.t  (** -> in predicates like: std.exists or in parametric type abbreviations. *)
  | AssumedFunctional  (** -> variadic predicates: never backtrack *)
  | Arrow of Mode.t * dtype * dtype  (** -> abstractions *)
  | Any
[@@deriving show, ord]

let rec pp_dtype fmt = function
  | Det -> Format.fprintf fmt "Det"
  | Rel -> Format.fprintf fmt "Rel"
  | BVar b -> Format.fprintf fmt "BVar %a" F.pp b
  | Any -> Format.fprintf fmt "Any"
  | Arrow (m, l, r) -> Format.fprintf fmt "(%a %a-> %a)" pp_dtype l Mode.pretty m pp_dtype r
  | AssumedFunctional -> Format.fprintf fmt "AssumedFunctional"
  | Exp l -> Format.fprintf fmt "Exp [%a]" (Format.pp_print_list pp_dtype) l

type dtype_abs =
  | Lam of F.t * dtype_abs  (** e.g: type abbrev (t X) (list X) becomes: Lam A (F (Arrow A Exp))*)
  | F of dtype
[@@deriving show, ord]

type dtype_loc = Loc.t * dtype_abs [@@deriving show, ord]
type t = { ty_abbr : dtype_loc F.Map.t; cmap : (F.t * dtype_abs) IdPos.Map.t } [@@deriving show, ord]

let arr m a b = Arrow (m, a, b)
let is_exp = function Exp _ -> true | _ -> false
let rec eat_lambdas = function Lam (_, b) -> eat_lambdas b | F b -> b

type env = t (* This is for the cleaner signatures in this files for objects with type t *)

let compare_functionality_loc a b = compare_dtype_abs (snd a) (snd b)
let compare_fname a b = compare_functionality_loc (snd a) (snd b)
let mk_func_map ty_abbr cmap = { ty_abbr; cmap }
let empty = { ty_abbr = F.Map.empty; cmap = IdPos.Map.empty }
let functionality_pi_sigma = arr Input (arr Input Any Det) Det

module Compilation = struct
  let rec subst ~loc sigma = function
    | BVar k as t -> (
        match F.Map.find_opt k sigma with
        | None -> t
        | Some (F f) -> f
        | Some (Lam (_, b)) -> error ~loc "type_abbrev not fully applied")
    | Arrow (m, l, r) -> arr m (subst ~loc sigma l) (subst ~loc sigma r)
    | Exp l -> Exp (List.map (subst ~loc sigma) l)
    | (AssumedFunctional | Det | Rel | Any) as t -> t

  (** 
  Used to beta reduce a type abbrev applied to arguments.
  
  Example:
  ```
    typeabbrev (list' A) (list A).  
    pred p i:(list' int).  
  ```
  
  The type of the input of p is reduced to (list A) after a beta-redex of
  `(A -> list A) int` where `(A -> list A)` is the unfold of `list'`
  
  Note: Type abbrev are always fully applied
*)
  let det_beta =
    let rec beta ~loc sigma = function
      | Lam (n, b), x :: xs -> beta ~loc (F.Map.add n (F x) sigma) (b, xs)
      | Lam (_, b), [] -> error ~loc "type_abbrev is not fully applied"
      | F t, [] -> subst ~loc sigma t
      | F _, _ :: _ -> anomaly ~loc "type_abbrev is too much applied"
    in
    beta F.Map.empty

  let scope_type_exp2det env (x : ScopedTypeExpression.t) =
    let rec type2func_app ~loc ~bvars (env : env) hd args =
      match F.Map.find_opt hd env.ty_abbr with
      | None -> Exp (List.map (type2func ~bvars env) args)
      | Some (_, f) -> det_beta ~loc (f, List.map (type2func ~bvars env) args)
    and type2func ~bvars (env : env) ScopedTypeExpression.{ it; loc } =
      match it with
      | ScopedTypeExpression.Const (_, c) when F.Set.mem c bvars -> BVar c
      | Const (_, c) -> type2func_app ~loc ~bvars env c []
      | App (_, c, x, xs) -> type2func_app ~loc ~bvars env c (x :: xs)
      | Arrow (_, Variadic, _, _) -> AssumedFunctional
      | Arrow (m, NotVariadic, l, r) -> arr m (type2func ~bvars env l) (type2func ~bvars env r)
      | Any -> Any
      | Prop Function -> Det
      | Prop Relation -> Rel
    in
    let rec type2func_lam ~bvars type_abbrevs = function
      | ScopedTypeExpression.Lam (n, t) ->
          let loc, r = type2func_lam ~bvars:(F.Set.add n bvars) type_abbrevs t in
          (loc, Lam (n, r))
      | Ty t -> (t.loc, F (type2func ~bvars type_abbrevs t))
    in
    type2func_lam ~bvars:F.Set.empty env x.value

  let type_ass_2func ~loc env (t : TypeAssignment.t MutableOnce.t) =
    let get_mutable v = match MutableOnce.get v with TypeAssignment.Val v -> v in
    let rec type2func_app ~loc (env : env) c args =
      match F.Map.find_opt c env.ty_abbr with
      | None -> Exp (List.map (type_ass_2func ~loc env) args)
      | Some (_, f) -> det_beta ~loc (f, List.map (type_ass_2func ~loc env) args)
    and type_ass_2func ~loc (env : env) = function
      | TypeAssignment.Prop Function -> Det
      | Prop Relation -> Rel
      | Any -> Any
      | Cons n -> type2func_app ~loc env n []
      | App (n, x, xs) -> type2func_app ~loc env n (x :: xs)
      | Arr (_, Variadic, _, _) -> AssumedFunctional
      | Arr (TypeAssignment.MVal m, NotVariadic, l, r) -> arr m (type_ass_2func ~loc env l) (type_ass_2func ~loc env r)
      | Arr (MRef m, NotVariadic, l, r) when MutableOnce.is_set m ->
          type_ass_2func ~loc env (Arr (MutableOnce.get m, NotVariadic, l, r))
      (*
         The typical example for the following case is a predicate quantified by a pi,
         an example can be found in tests/sources/findall.elpi
      *)
      | Arr (MRef m, NotVariadic, l, r) -> Arrow (Output, type_ass_2func ~loc env l, type_ass_2func ~loc env r)
      | UVar a ->
          if MutableOnce.is_set a then type_ass_2func ~loc (env : env) (get_mutable a)
          else BVar (MutableOnce.get_name a)
    in
    type_ass_2func ~loc env (get_mutable t)
end

module Aux = struct
  let rec min ~loc f1 f2 =
    match (f1, f2) with
    | Det, _ | _, Det -> Det
    | Rel, Rel -> Rel
    | a, (Any | BVar _) | (Any | BVar _), a -> a
    | Exp l1, Exp l2 -> Exp (List.map2 (min ~loc) l1 l2)
    | Arrow (m1, _, r1), Arrow (m2, _, _) when m1 <> m2 -> error ~loc "Mode mismatch"
    | Arrow (Input, l1, r1), Arrow (_, l2, r2) -> Arrow (Input, max ~loc l1 l2, min ~loc r1 r2)
    | Arrow (Output, l1, r1), Arrow (_, l2, r2) -> Arrow (Output, min ~loc l1 l2, min ~loc r1 r2)
    | AssumedFunctional, _ | _, AssumedFunctional -> AssumedFunctional
    | a, b -> Format.asprintf "Computing min between %a and %a" pp_dtype a pp_dtype b |> anomaly ~loc

  and max ~loc f1 f2 =
    match (f1, f2) with
    | Rel, _ | _, Rel -> Rel
    | Det, Det -> Det
    | _, Any | Any, _ -> Any
    | Exp l1, Exp l2 -> Exp (List.map2 (max ~loc) l1 l2)
    | Arrow (m1, _, r1), Arrow (m2, _, _) when m1 <> m2 -> error ~loc "Mode mismatch"
    | Arrow (Input, l1, r1), Arrow (_, l2, r2) -> Arrow (Input, min ~loc l1 l2, max ~loc r1 r2)
    | Arrow (Output, l1, r1), Arrow (_, l2, r2) -> Arrow (Output, max ~loc l1 l2, max ~loc r1 r2)
    | AssumedFunctional, _ | _, AssumedFunctional -> AssumedFunctional
    | BVar _, a | a, BVar _ -> a
    | a, b -> Format.asprintf "Computing max between %a and %a" pp_dtype a pp_dtype b |> anomaly ~loc

  let rec maximize = function
    | Rel | Det -> Rel
    | Exp l -> Exp (List.map maximize l)
    | Arrow (Input, l, r) -> Arrow (Input, minimize l, maximize r)
    | Arrow (Output, l, r) -> Arrow (Output, maximize l, maximize r)
    | AssumedFunctional -> AssumedFunctional
    | Any -> Any
    | BVar b -> BVar b

  and minimize = function
    | Rel | Det -> Det
    | Exp l -> Exp (List.map minimize l)
    | Arrow (Input, l, r) -> Arrow (Input, maximize l, minimize r)
    | Arrow (Output, l, r) -> Arrow (Output, minimize l, minimize r)
    | AssumedFunctional -> AssumedFunctional
    | Any -> Any
    | BVar b -> BVar b

  let ( <<= ) ~loc a b =
    let rec aux ~loc a b =
      match (a, b) with
      | BVar _, _ | _, BVar _ -> true
      | Exp l1, Exp l2 -> List.for_all2 (aux ~loc) l1 l2
      | _, Any -> true
      | Any, _ -> b = maximize b
      | _, Rel | Det, _ | AssumedFunctional, _ -> true
      | Rel, _ -> false
      | _, AssumedFunctional -> error ~loc (Format.asprintf "Cannot compare AssumedFunctional with different dtype")
      | Arrow (m1, l1, r1), Arrow (m2, l2, r2) -> aux l2 l1 ~loc && aux r1 r2 ~loc
      | Arrow _, _ | _, Arrow _ | Exp _, _ ->
          anomaly ~loc (Format.asprintf "Type error in comparing %a and %a" pp_dtype a pp_dtype b)
    in
    let res = aux a b ~loc in
    res
end

let ( <<= ) = Aux.( <<= )

module EnvMaker (M : Map.S) : sig
  type t [@@deriving show]

  val add : loc:Loc.t -> v:dtype -> t -> M.key -> t
  val get : t -> M.key -> dtype option
  val mem : t -> M.key -> bool
  val clone : t -> t
  val empty : t
end = struct
  type t = dtype ref M.t [@@deriving show]

  let add ~loc ~(v : dtype) (env : t) (n : M.key) : t =
    match M.find_opt n env with
    | None ->
        let res = M.add n (ref v) env in
        res
    | Some v' ->
        v' := Aux.min ~loc v !v';
        env

  let remove a b = M.remove b a
  let get (env : t) (k : M.key) = Option.map ( ! ) (M.find_opt k env)
  let mem env k = M.mem k env
  let empty = M.empty
  let clone : t -> t = M.map (fun v -> ref !v)
end

module Var = EnvMaker (F.Map)

module Ctx = struct
  include EnvMaker (Scope.Map)

  let add_oname ~loc oname f ctx =
    match oname with None -> ctx | Some (scope, name, tya) -> add ~loc ctx (name, scope) ~v:(f tya)

  let get_oname oname ctx = match oname with None -> None | Some (scope, name, _) -> get ctx (name, scope)
end

module Format = struct
  include Format

  (* let eprintf : ('a, Format.formatter, unit) format -> 'a = fun e -> Format.ifprintf Format.std_formatter e *)
end

let get_dtype uf ~env ~ctx ~var ~loc ~is_var (t, name, tya) =
  Format.eprintf "Getting functionality of %a which is_var? %b@." F.pp name is_var;
  let get_ctx = function
    | None -> anomaly ~loc (Format.asprintf "Bound var %a should be in the local map" F.pp name)
    | Some e -> e
  in
  let get_var = function None -> Any | Some e -> e in
  let get_con x =
    if F.equal name F.mainf then Rel (*TODO: what if the main has arguments?*)
    else if x = Scope.dummy_type_decl_id then Any
    else if F.equal F.eqf name then arr Output (BVar (F.from_string "A")) (arr Output (BVar (F.from_string "A")) Det)
    else
      let id' = UF.find uf x in
      (* The if instruction below is a sanity check: if x has a parent in the uf, then x should
         not be in the map, othewise the same piece of information would be store
         twice in the map, which is unwanted *)
      if x <> id' then assert (not (IdPos.Map.mem x env.cmap));
      match IdPos.Map.find_opt id' env.cmap with
      (* find_opt is for types with unkown signature.
         their type has been inferred by the typechecker *)
      | None -> Compilation.type_ass_2func ~loc env tya
      | Some (name, func) ->
          if F.equal F.pif name || F.equal F.sigmaf name then functionality_pi_sigma else 
            (* eat_lambdas func *)
            Compilation.type_ass_2func ~loc env tya
  in
  let det_head =
    if is_var then get_var @@ Var.get var name
    else match t with Scope.Bound b -> get_ctx @@ Ctx.get ctx (name, b) | Global g -> get_con g.decl_id
  in
  Format.eprintf "The functionality of %a is %a (its type is %a)@." F.pp name pp_dtype det_head
    TypeAssignment.pretty_mut_once_raw (TypeAssignment.deref tya);
  det_head

let spill_err ~loc = anomaly ~loc "Everything should have already been spilled"

class good_call =
  object
    val mutable obj = None
    method is_good = Option.is_none obj
    method is_wrong = Option.is_some obj
    method set_wrong (l : Loc.t) = obj <- Some l
    method show = match obj with None -> "true" | Some e -> Format.asprintf "false (%a)" Loc.pp e
    method get_loc : Loc.t = Option.get obj
  end

module Checker = struct
  let rec get_tl = function Arrow (_, _, r) -> get_tl r | e -> e

  exception IGNORE

  let rec infer uf ~env ~ctx ~var t : dtype * good_call =
    let rec infer_fold ~loc ctx d tl =
      let b = new good_call in
      let rec aux d tl =
        match (d, tl) with
        | t, [] -> (t, b)
        | Arrow (Input, i, d), h :: tl ->
            let dy, b' = infer ctx h in
            Format.eprintf "After call to deduce in aa %a and is_good:%s; Expected is %a@." pp_dtype dy b'#show pp_dtype
              i;
            if b'#is_wrong then (
              (* If the recursive call is wrong, we stop and return bottom *)
              b#set_wrong b'#get_loc;
              (Any, b))
            else if not ((dy <<= i) ~loc) then (
              (* If preconditions are not satisfied, we stop and return bottom *)
              b#set_wrong loc;
              (Any, b))
            else aux d tl (* The recursive call is correct *)
        | Arrow (Output, _, d), _ :: tl -> aux d tl
        | (AssumedFunctional | BVar _ | Any), _ -> (d, new good_call)
        | (Det | Rel | Exp _), _ :: _ ->
            Format.asprintf "deduce: Type error, found dtype %a and arguments %a" pp_dtype d
              (pplist ScopedTerm.pretty ",") tl
            |> anomaly ~loc
      in
      aux d tl
    and infer_app ctx ~loc is_var s tl = infer_fold ~loc ctx (get_dtype uf ~env ~ctx ~var ~loc ~is_var s) tl
    and infer_comma ctx ~loc args d =
      match args with
      | [] -> d
      | ScopedTerm.{ it = Const (_, cut, _); _ } :: xs when F.equal F.cutf cut ->
          infer_comma ctx ~loc xs (Det, new good_call)
      | x :: xs -> infer_comma ctx ~loc xs (infer ctx x)
    and infer ctx ScopedTerm.({ it; ty; loc } as t) : dtype * good_call =
      Format.eprintf "--> Infer of %a@." ScopedTerm.pretty_ it;
      match it with
      | ScopedTerm.Const b -> infer_app ~loc ctx false b []
      | Var (b, xs) -> infer_app ~loc ctx true b xs
      | App ((Global _, name, _), x, xs) when name = F.andf ->
          Format.eprintf "Calling deduce on a comma separated list of subgoals@.";
          infer_comma ctx ~loc (x :: xs) (Det, new good_call)
      | App (b, x, xs) -> infer_app ~loc ctx false b (x :: xs)
      | Impl (true, c, b) ->
          check_clause uf ~env ~ctx ~var c |> ignore;
          infer ctx b
      | Impl (false, _, _) -> (check_clause uf ~env ~ctx ~var t, new good_call)
      | Lam (oname, _, c) -> (
          Format.eprintf "In lambda of infer, the ty is %a@." (MutableOnce.pp TypeAssignment.pp) ty;
          let dty = Compilation.type_ass_2func ~loc env ty in
          match dty with
          | Arrow (Input, l, _) ->
              let ctx = Ctx.add_oname ~loc oname (fun _ -> l) ctx in
              let r, b = infer ctx c in
              (Arrow (Input, l, r), b)
          | Arrow (Output, l, _) ->
              let ctx = Ctx.add_oname ~loc oname (fun _ -> Any) ctx in
              let r, b = infer ctx c in
              Format.eprintf "The output binder is %a@." (Format.pp_print_option pp_dtype) (Ctx.get_oname oname ctx);
              (* Option.iter (fun x -> assert ((x <<= l) ~loc)) (Ctx.get_oname oname ctx); *)
              (* TODO: should I check that the dtype of oname in Ctx is <<= then l?  *)
              (Arrow (Output, l, r), b)
          | Any -> (Any, new good_call)
          | _ -> anomaly ~loc (Format.asprintf "Found lambda term with dtype %a" pp_dtype dty))
      | Discard ->
          Format.eprintf "Calling type_ass_2func in Discard@.";
          (Any, new good_call)
      | CData _ -> (Exp [], new good_call)
      | Cast (t, _) -> infer ctx t
      | Spill (_, _) -> spill_err ~loc
    in
    infer ctx t

  and infer_output uf ~env ~ctx ~var ScopedTerm.{ it; ty; loc } =
    Format.eprintf "Calling deduce output on %a@." ScopedTerm.pretty_ it;
    let rec aux dtype args =
      match (dtype, args) with
      | Arrow (Input, _, r), _ :: tl -> aux r tl
      | Arrow (Output, l, r), hd :: tl ->
          let det, is_good = infer uf ~env ~ctx ~var hd in
          if is_good#is_good && (det <<= l) ~loc then aux r tl
          else if is_good#is_good then
            error ~loc:hd.loc
            @@ Format.asprintf "Invalid determinacy of output term %a.\n Expected: %a\n Found: %a" ScopedTerm.pretty hd
                 pp_dtype l pp_dtype det
          else
            error ~loc:is_good#get_loc
            @@ Format.asprintf "The term %a has not the right determinacy (it should be %a)" ScopedTerm.pretty hd
                 pp_dtype l
      | _ -> ()
    in
    match it with
    | Const _ -> ()
    (* TODO: add case for pi, comma and = *)
    | App (b, x, xs) -> aux (get_dtype uf ~env ~ctx ~var ~loc ~is_var:false b) (x :: xs)
    | Var (b, xs) -> aux (get_dtype uf ~env ~ctx ~var ~loc ~is_var:true b) xs
    | _ -> anomaly ~loc @@ Format.asprintf "Invalid term in deduce output %a." ScopedTerm.pretty_ it

  and assume uf ~env ~ctx ~var d t =
    Format.eprintf "Calling assume on %a@." ScopedTerm.pretty t;
    let var = ref var in
    let add ~loc ~v vname =
      let m = Var.add ~loc !var vname ~v in
      var := m
    in
    let rec assume_fold ~was_input ~was_data ~loc ctx d (tl : ScopedTerm.t list) =
      match (d, tl) with
      | t, [] -> ()
      | Arrow (Input, i, d), h :: tl ->
          assume ~was_input:true ctx i h;
          assume_fold ~was_input ~was_data ~loc ctx d tl
      (* NOTE: if Output && is_data && was_input then assume i h; assume_fold ~loc ctx d tl *)
      | Arrow (Output, i, d), h :: tl -> 
          if was_input && was_data then assume ~was_input ctx i h;
          assume_fold ~was_input ~was_data ~loc ctx d tl
      | (AssumedFunctional | BVar _ | Any), _ -> ()
      | (Det | Rel | Exp _), _ :: _ ->
          Format.asprintf "assume: Type error, found dtype %a and arguments %a@." pp_dtype d
            (pplist ScopedTerm.pretty ",") tl
          |> anomaly ~loc
    and assume_app ~was_input ctx ~loc ~is_var d ((t, name, _) as s) tl =
      Format.eprintf "Calling assume_app on: %a with dtype %a with args [%a] and is var:%b@." F.pp name pp_dtype d
        (pplist ~boxed:true ScopedTerm.pretty " ; ")
        tl is_var;
      (if tl = [] then
         if is_var then add ~loc ~v:d name
         else match t with Scope.Bound b -> Ctx.add ctx ~v:d ~loc (name, b) |> ignore | Global g -> ()
       else
         let det_head = get_dtype uf ~env ~ctx ~var:!var ~loc ~is_var s in
         (* NOTE: if d = Exp _ then assume_fold ~is_data:true  *)
         assume_fold ~was_input ~was_data:(is_exp d) ~loc ctx det_head tl);
      Format.eprintf "The map after call to assume_app is %a@." Var.pp !var
    and assume ~was_input ctx d ScopedTerm.({ ty; loc; it } as t) : unit =
      Format.eprintf "Assume of %a with dtype %a (was_input:%b)@." ScopedTerm.pretty_ it pp_dtype d was_input;
      match it with
      | Const b -> assume_app ~was_input ctx ~loc ~is_var:false d b []
      | Var (b, tl) -> assume_app ~was_input ctx ~loc ~is_var:true d b tl
      (* TODO: add case for pif and sigmaf ? *)
      | App ((Global _, name, _), x, xs) when name = F.andf -> List.iter (assume ~was_input ctx d) (x :: xs)
      | App (b, hd, tl) -> assume_app ~was_input ctx ~loc ~is_var:false d b (hd :: tl)
      | Discard -> ()
      | Impl (true, h, b) ->
          check_clause uf ~env ~ctx ~var:!var h |> ignore;
          assume ~was_input ctx d b
      | Impl (false, _H, _B) -> check_clause uf ~env ~ctx ~var:!var t |> ignore
      | Lam (oname, _, c) -> (
          match d with
          | Arrow (Input, l, r) ->
              let ctx = Ctx.add_oname ~loc oname (fun _ -> l) ctx in
              assume ~was_input ctx r c
          | Arrow (Output, l, r) ->
              let ctx = Ctx.add_oname ~loc oname (fun _ -> l) ctx in
              assume ~was_input ctx r c
          | Any -> ()
          | _ -> anomaly ~loc (Format.asprintf "Found lambda term with dtype %a" pp_dtype d))
      | CData _ -> ()
      | Spill _ -> spill_err ~loc
      | Cast (t, _) -> assume ~was_input ctx d t
    in
    assume ~was_input:false ctx d t;
    !var

  and assume_output uf ~env ~ctx ~var d tl : Var.t =
    let rec assume_output dtype args var =
      match (dtype, args) with
      | Arrow (Input, _, r), _ :: tl -> assume_output r tl var
      | Arrow (Output, l, r), hd :: tl ->
          Format.eprintf "Call assume of %a with dtype:%a@." ScopedTerm.pretty hd pp_dtype l;
          let var = assume uf ~env ~ctx ~var l hd in
          assume_output r tl var
      | _ -> var
    in
    assume_output d tl var

  (* returns the updated environment, the dtype of the term and the loc of the term with max dtype *)
  and check uf ~env ~ctx ~var d t =
    let var = ref var in
    let rec check_app ctx ~loc d ~is_var b tl tm =
      Format.eprintf "-- Entering check_app with term %a@." ScopedTerm.pretty tm;
      let d', is_good = infer uf ~env ~ctx ~var:!var tm in
      Format.eprintf "-- Checked term dtype is %a and is_good is %s@." pp_dtype d' is_good#show;
      if is_good#is_good then (
        let det = get_dtype uf ~env ~ctx ~var:!var ~is_var b ~loc in
        Format.eprintf "Assuming output of %a with dtype : %a@." ScopedTerm.pretty tm pp_dtype det;
        var := assume_output uf ~env ~ctx ~var:!var det tl);
      Format.eprintf "Before error %a <<= %a@." pp_dtype d' pp_dtype d;
      if is_good#is_good && (d' <<= d) ~loc then Aux.max ~loc (get_tl d) (get_tl d') else Rel
    and check_comma ctx ~loc d args =
      match args with
      | [] -> d
      | x :: xs ->
          Format.eprintf "Checking comma with first term %a@." ScopedTerm.pretty x;
          check_comma ctx ~loc (check ~ctx d x) xs
    and check ~ctx d ScopedTerm.({ ty; it; loc } as t) =
      match it with
      | Impl (true, h, b) ->
          (* We clone not to change the ctx and var in the call for b *)
          check_clause uf ~env ~ctx ~var:!var h |> ignore;
          check ~ctx d b
      | Const (Global _, cut, _) when F.equal F.cutf cut -> Det
      (* Cons and nil case may appear in prop position for example in : `f :- [print a, print b, a].` *)
      | App ((Global _, cons, _), x, [ xs ]) when F.equal F.consf cons -> check ~ctx (check ~ctx d x) xs
      | Const (Global _, nil, _) when F.equal F.nilf nil -> d
      | App ((Global _, comma, _), x, xs) when F.equal F.andf comma -> check_comma ctx ~loc d (x :: xs)
      (* !! predicate with arity 0, may create choice points, example:
          pred x.
          func f -> int.
          f Y :- (x :- Y = 3) => (x :- Y = 4) => x.
      *)
      | Const b -> check_app ctx ~loc d ~is_var:false b [] t
      | Var (b, xs) -> check_app ctx ~loc d ~is_var:true b xs t
      | App ((Global _, name, _), l, [ r ]) when name = F.eqf ->
          let d1, b = infer uf ~env ~ctx ~var:!var l in
          (if b#is_good then
             let d2, b = infer uf ~env ~ctx ~var:!var r in
             if b#is_good then (
               Format.eprintf "In equality calling min between the two terms %a and %a@." ScopedTerm.pretty l
                 ScopedTerm.pretty r;
               let m = Aux.min ~loc d1 d2 in
               Format.eprintf "The minimum between %a and %a is %a@." pp_dtype d1 pp_dtype d2 pp_dtype m;
               var := assume uf ~env ~ctx ~var:!var m l;
               var := assume uf ~env ~ctx ~var:!var m r));
          d
      | App ((Global _, ps, _), { it = Lam (oname, _, b) }, []) when ps = F.pif || ps = F.sigmaf ->
          let ctx = Ctx.add_oname ~loc oname (Compilation.type_ass_2func ~loc env) ctx in
          check ~ctx d b
      | App (b, x, xs) -> check_app ctx ~loc d ~is_var:false b (x :: xs) t
      | Cast (b, _) -> check ~ctx d b
      | Spill (b, _) -> spill_err ~loc
      | CData _ -> anomaly ~loc "Found CData in prop position"
      | Lam _ -> anomaly ~loc "Lambda-abstractions are not props"
      | Discard -> anomaly ~loc "Discard found in prop position"
      | Impl (false, hd, tl) -> anomaly ~loc "Found clause in prop position"
    in
    (!var, check ~ctx d t)

  and check_clause uf ~env ~ctx ~var ScopedTerm.({ it; ty; loc } as t) =
    let ctx = ref (Ctx.clone ctx) in
    let add_ctx ~loc k v = ctx := Ctx.add ~loc !ctx k ~v in
    let var = Var.clone var in
    let assume_hd b is_var (tm : ScopedTerm.t) =
      (* let _ =
           let do_filter = false in
           let only_check = "main" in
           let loc = ".*test38.elpi.*" in
           let _, name, _ = b in
           if
             do_filter
             && Re.Str.(string_match (regexp only_check) (F.show name) 0 && string_match (regexp loc) (Loc.show tm.loc) 0)
                |> not
           then raise IGNORE
         in *)
      let det_hd = get_dtype uf ~env ~ctx:!ctx ~var ~loc:tm.loc ~is_var b in
      Format.eprintf "Calling assume in hd for terms list %a@." ScopedTerm.pretty tm;
      (det_hd, assume uf ~env ~ctx:!ctx ~var det_hd tm)
    in
    let rec aux ScopedTerm.{ it; loc } =
      match it with
      | Impl (false, ({ it = Const b } as hd), bo) -> (assume_hd b false hd, hd, Some bo)
      | Impl (false, ({ it = App (b, _, _) } as hd), bo) -> (assume_hd b false hd, hd, Some bo)
      | Const b -> (assume_hd b false t, t, None)
      | App ((Global _, n, _), { it = Lam (oname, ty, body) }, []) when F.equal F.pif n || F.equal F.sigmaf n ->
          Option.iter
            (fun (scope, name, tya) -> add_ctx ~loc (name, scope) (Compilation.type_ass_2func ~loc env tya))
            oname;
          aux body
      | App (b, _, _) -> (assume_hd b false t, t, None)
      | Var (b, _) -> (assume_hd b true t, t, None)
      | _ -> anomaly ~loc @@ Format.asprintf "Found term %a in prop position" ScopedTerm.pretty_ it
    in

    Format.eprintf "=================================================@.";
    Format.eprintf "Checking clause %a@." ScopedTerm.pretty t;
    Format.eprintf "The var map is %a@." Var.pp var;
    Format.eprintf "** START CHECKING THE CLAUSE@.";
    let (det_hd, var), hd, body = aux t in
    let var, det_body = Option.(map (check uf ~env ~ctx:!ctx ~var Det) body |> value ~default:(var, Det)) in
    Format.eprintf "** END CHECKING THE CLAUSE@.";
    Format.eprintf "The var map is %a and det_body is %a@." Var.pp var pp_dtype det_body;

    let det_pred = get_tl det_hd in
    if not @@ (det_body <<= det_pred) ~loc then
      error ~loc "Determinacy checking error, expected a functional body, but inferred relational";
    Format.eprintf "** Start checking outputs@.";
    infer_output uf ~env ~ctx:!ctx ~var hd;
    det_pred
end

let check_clause : uf:IdPos.UF.t -> loc:Loc.t -> env:t -> ScopedTerm.t -> unit =
 fun ~uf ~loc ~env t ->
  try Checker.check_clause uf ~env ~ctx:Ctx.empty ~var:Var.empty t |> ignore with Checker.IGNORE -> ()

let add_type ~loc is_type_abbr env ~n ~id v =
  if is_type_abbr && F.Map.mem n env.ty_abbr then error (Format.asprintf "Adding again type_abbrev %a" F.pp n);
  if is_type_abbr then
    let ty_abbr = F.Map.add n (loc, v) env.ty_abbr in
    mk_func_map ty_abbr env.cmap
  else
    let cmap = IdPos.Map.add id (n, v) env.cmap in
    mk_func_map env.ty_abbr cmap

let remove t k = { t with cmap = IdPos.Map.remove k t.cmap }

let merge f1 f2 =
  let pp_fname fmt (x, y) = Format.fprintf fmt "(%a,%a)" F.pp x pp_dtype_loc y in
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

class merger (all_func : env) =
  object (self)
    val mutable all_func = all_func
    val mutable local_func = empty

    method private add_func is_ty_abbr id ty =
      let loc, func = Compilation.scope_type_exp2det all_func ty in
      let n = ty.name in
      if is_ty_abbr then all_func <- add_type ~loc is_ty_abbr ~id ~n all_func func;
      local_func <- add_type ~loc is_ty_abbr ~id ~n local_func func

    method get_all_func = all_func
    method get_local_func = local_func
    method add_ty_abbr = self#add_func true
    method add_func_ty_list ty id_list = List.iter2 (self#add_func false) id_list ty
    method merge : env = merge all_func local_func
  end
