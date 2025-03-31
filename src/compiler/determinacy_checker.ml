(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Elpi_util.Util
open Elpi_parser.Ast
open Compiler_data
module C = Constants
module UF = Symbol.UF

exception DetError of string * Loc.t
exception FatalDetError of string * Loc.t
exception LoadFlexClause

type dtype =
  | Det  (** -> for deterministic preds *)
  | Rel  (** -> for relational preds *)
  | Exp of dtype list  (** -> for kinds like list, int, string *)
  | BVar of F.t  (** -> in predicates like: std.exists or in parametric type abbreviations. *)
  | Arrow of Mode.t * Structured.variadic * dtype * dtype  (** -> abstractions *)
  | Any
[@@deriving show, ord]

let rec pp_dtype fmt = function
  | Det -> Format.fprintf fmt "Det"
  | Rel -> Format.fprintf fmt "Rel"
  | BVar b -> Format.fprintf fmt "BVar %a" F.pp b
  | Any -> Format.fprintf fmt "Any"
  | Arrow (m, Variadic, l, r) -> Format.fprintf fmt "(Variadic %a %a-> %a)" pp_dtype l Mode.pretty m pp_dtype r
  | Arrow (m, _, l, r) -> Format.fprintf fmt "(%a %a-> %a)" pp_dtype l Mode.pretty m pp_dtype r
  | Exp l -> Format.fprintf fmt "Exp [%a]" (Format.pp_print_list pp_dtype) l

type t = (TypeAssignment.skema * Loc.t) F.Map.t [@@deriving show, ord]

let arr m ~v a b = Arrow (m, v, a, b)
let is_exp = function Exp _ -> true | _ -> false
let is_arr = function Arrow _ -> true | _ -> false
let choose_variadic v full right = if v = Structured.Variadic then full else right
let empty_env = F.Map.empty

module Compilation = struct
  let get_mutable v = match MutableOnce.get v with TypeAssignment.Val v -> v

  let type_ass_2func ~loc (env : t) t =
    let rec type2func_app ~loc c args =
      match F.Map.find_opt c env with
      | None -> Exp (List.map (type_ass_2func ~loc) args)
      | Some (f, _) ->
          let ta_app = TypeAssignment.apply f args in
          type_ass_2func ~loc ta_app
    and type_ass_2func ~loc = function
      | TypeAssignment.Prop Function -> Det
      | Prop Relation -> Rel
      | Any -> Any
      | Cons n -> type2func_app ~loc n []
      | App (n, x, xs) -> type2func_app ~loc n (x :: xs)
      | Arr (TypeAssignment.MVal m, v, l, r) -> arr m ~v (type_ass_2func ~loc l) (type_ass_2func ~loc r)
      | Arr (MRef m, v, l, r) when MutableOnce.is_set m ->
          type_ass_2func ~loc (Arr (MutableOnce.get m, NotVariadic, l, r))
      (*
          The typical example for the following case is a predicate quantified by a pi,
          an example can be found in tests/sources/findall.elpi
      *)
      | Arr (MRef m, v, l, r) -> arr ~v Output (type_ass_2func ~loc l) (type_ass_2func ~loc r)
      | UVar a -> if MutableOnce.is_set a then type_ass_2func ~loc (get_mutable a) else BVar (MutableOnce.get_name a)
    in
    type_ass_2func ~loc t

  let type_ass_2func_mut ~loc (env : t) t = type_ass_2func ~loc env (get_mutable t)
end

module Aux = struct
  let check_variadic f1 f2 mode d1 v1 l1 r1 d2 v2 l2 r2 =
    match (v1, v2) with
    | Structured.(Variadic, Variadic) -> Arrow (mode, v1, f1 l1 l2, f2 r1 r2)
    | NotVariadic, NotVariadic -> Arrow (mode, v1, f1 l1 l2, f2 r1 r2)
    | Variadic, NotVariadic -> Arrow (mode, v1, f1 l1 l2, f2 d1 r2)
    | NotVariadic, Variadic -> Arrow (mode, v1, f1 l1 l2, f2 r1 d2)

  let rec min_max ~loc ~d1 ~d2 f1 f2 =
    if f1 = d1 || f2 = d1 then d1
    else
      match (f1, f2) with
      | Det, Det -> Det
      | Rel, Rel -> Rel
      | a, (Any | BVar _) | (Any | BVar _), a -> a
      | Exp l1, Exp l2 -> (
          try Exp (List.map2 (min_max ~loc ~d1 ~d2) l1 l2)
          with Invalid_argument _ -> anomaly ~loc "detCheck: min_max invalid exp_length")
      | Arrow (m1, _, _, r1), Arrow (m2, _, _, _) when m1 <> m2 -> anomaly ~loc "Mode mismatch"
      | Arrow (Input, v1, l1, r1), Arrow (_, v2, l2, r2) ->
          check_variadic (min_max ~loc ~d1:d2 ~d2:d1) (min_max ~loc ~d1 ~d2) Input f1 v1 l1 r1 f2 v2 l2 r2
      | Arrow (Output, v1, l1, r1), Arrow (_, v2, l2, r2) ->
          check_variadic (min_max ~loc ~d1 ~d2) (min_max ~loc ~d1 ~d2) Output f1 v1 l1 r1 f2 v2 l2 r2
      | Arrow (_, Variadic, _, r), f2 -> min_max ~loc ~d1 ~d2 r f2
      | f2, Arrow (_, Variadic, _, r) -> min_max ~loc ~d1 ~d2 r f2
      | _ -> Format.asprintf "DetCheck: min between %a and %a" pp_dtype f1 pp_dtype f2 |> anomaly ~loc

  let min = min_max ~d1:Det ~d2:Rel
  let max = min_max ~d1:Rel ~d2:Det

  let rec minimize_maximize ~loc ~d1 ~d2 d =
    match d with
    | Det | Rel -> d1
    | Exp l -> Exp (List.map (minimize_maximize ~loc ~d1 ~d2) l)
    | Arrow (Input, v, l, r) ->
        Arrow (Input, v, minimize_maximize ~loc ~d1:d2 ~d2:d1 l, minimize_maximize ~loc ~d1 ~d2 r)
    | Arrow (Output, v, l, r) -> Arrow (Output, v, minimize_maximize ~loc ~d1 ~d2 l, minimize_maximize ~loc ~d1 ~d2 r)
    | Any -> Any
    | BVar b -> BVar b

  let minimize = minimize_maximize ~d1:Det ~d2:Rel
  let maximize = minimize_maximize ~d1:Rel ~d2:Det

  let wrong_type ~loc a b =
    anomaly ~loc @@ Format.asprintf "DetCheck: Typing invariant broken: %a <<= %a\n%!" pp_dtype a pp_dtype b

  let wrong_bvars ~loc v1 v2 =
    anomaly ~loc @@ Format.asprintf "DetCheck: <<=: TC did not unify two unif vars (%a and %a)" F.pp v1 F.pp v2

  let ( <<= ) ~loc a b =
    let rec aux ~loc a b =
      match (a, b) with
      | _, Any -> true
      | Any, _ -> b = maximize ~loc b (* TC may accept A = any, so we do too *)
      | BVar v1, BVar v2 -> F.equal v1 v2 || wrong_bvars ~loc v1 v2
      | BVar _, _ | _, BVar _ -> wrong_type ~loc a b
      | Exp l1, Exp l2 -> ( try List.for_all2 (aux ~loc) l1 l2 with Invalid_argument _ -> wrong_type ~loc a b)
      | Arrow (_, NotVariadic, l1, r1), Arrow (_, NotVariadic, l2, r2) -> aux l2 l1 ~loc && aux r1 r2 ~loc
      | Arrow (_, NotVariadic, l1, r1), Arrow (_, Variadic, l2, r2) -> aux l2 l1 ~loc && aux r1 b ~loc
      | Arrow (_, Variadic, l1, r1), Arrow (_, NotVariadic, l2, r2) -> aux l2 a ~loc && aux r1 r2 ~loc
      | Arrow (_, Variadic, l1, r1), Arrow (_, Variadic, l2, r2) -> aux l2 l1 ~loc && aux r1 r2 ~loc
      (* Left is variadic, Right is not an arrow -> we eat the arrow and continue *)
      | Arrow (_, Variadic, _, r), d -> aux r d ~loc
      (* Left is not an arrow, Right is variadic -> we eat the arrow and continue *)
      | d, Arrow (_, Variadic, _, r) -> aux d r ~loc
      | Arrow _, _ | _, Arrow _ | Exp _, _ -> wrong_type ~loc a b
      (* Below base case *)
      | _, Rel -> true (* rel is the sup *)
      | Rel, _ -> false
      | Det, _ -> true (* det is the inf *)
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
  val remove : t -> M.key -> t
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

module UVar = EnvMaker (F.Map)

module BVar = struct
  include EnvMaker (Scope.Map)

  let add_oname ~loc oname f ctx =
    match oname with None -> ctx | Some (scope, name, tya) -> add ~loc ctx (name, scope) ~v:(f tya)

  let get_oname oname ctx = match oname with None -> None | Some (scope, name, _) -> get ctx (name, scope)
  let remove_oname ctx oname = match oname with None -> ctx | Some (scope, name, _) -> remove ctx (name, scope)
end

module Format = struct
  include Format

  let eprintf : ('a, Format.formatter, unit) format -> 'a = fun e -> Format.ifprintf Format.std_formatter e
  let eprintf = eprintf
end

let get_dtype ~env ~ctx ~var ~loc ~is_var (t, name, tya) =
  let get_ctx = function
    | None -> anomaly ~loc (Format.asprintf "Bound var %a should be in the local map" F.pp name)
    | Some e -> e
  in
  let get_var = function None -> Any | Some e -> e in
  let get_con x =
    if F.equal name F.mainf then Rel (*TODO: what if the main has arguments?*)
    else if x = None then Any
    else Compilation.type_ass_2func_mut ~loc env tya
  in
  let det_head =
    if is_var then get_var @@ UVar.get var name
    else match t with Scope.Bound b -> get_ctx @@ BVar.get ctx (name, b) | Global g -> get_con g.decl_id
  in
  Format.eprintf "The type of %a is %a@." F.pp name pp_dtype det_head;
  Format.eprintf "The dtype of %a is %a@." F.pp name pp_dtype det_head;
  Format.eprintf "The functionality of %a is %a (its type is %a)@." F.pp name pp_dtype det_head
    TypeAssignment.pretty_mut_once_raw (TypeAssignment.deref tya);
  det_head

let spill_err ~loc = anomaly ~loc "DetCheck: Everything should have already been spilled"

class good_call =
  object
    val mutable obj = None
    method is_good = Option.is_none obj
    method is_wrong = Option.is_some obj
    method set_wrong (l : Loc.t) = obj <- Some l
    method set_good = obj <- None
    method show = match obj with None -> "true" | Some e -> Format.asprintf "false (%a)" Loc.pp e
    method get_loc : Loc.t = Option.get obj
  end

let check_clause ~(env:t) (t:ScopedTerm.t) : bool =
  let is_quantifier (b, f, _) =
    (match b with Scope.Global _ -> true | _ -> false) && (F.equal F.pif f || F.equal F.sigmaf f)
  in

  let cnt = ref 0 in
  let emit () =
    incr cnt;
    F.from_string ("*dummy" ^ string_of_int !cnt)
  in
  let rec get_tl = function Arrow (_, _, _, r) -> get_tl r | e -> e in

  (* let exception IGNORE in *)

  let is_cut ScopedTerm.{ it } = match it with Const (Global _, name, _) -> F.equal F.cutf name | _ -> false in

  let rec infer ~ctx ~var t : dtype * good_call =
    let rec infer_fold ~was_input ~was_data ~loc ctx d tl =
      let b = new good_call in
      let rec aux d tl =
        Format.eprintf "In recursive call for aux with list [%a], bool is %s@." (pplist ScopedTerm.pretty ", ") tl
          b#show;
        match (d, tl) with
        | Arrow (_, Variadic, _, t), [] -> (t, b)
        | t, [] -> (t, b)
        | Arrow (Input, v, l, r), h :: tl ->
            (if is_cut h then b#set_good
             else
               let dy, b' = infer ~was_input:true ctx h in
               Format.eprintf "After call to deduce in aux %a, its determinacy is %a and is_good:%s; Expected is %a@."
                 ScopedTerm.pretty h pp_dtype dy b'#show pp_dtype l;
               if b'#is_wrong then (* If the recursive call is wrong, we stop and return bottom *)
                 b#set_wrong b'#get_loc
               else if not ((dy <<= l) ~loc) then (
                 (* If preconditions are not satisfied, we stop and return bottom *)
                 b#set_wrong loc;
                 Format.eprintf "Invalid determinacy set b to wrong (%s)@." b#show));
            aux (choose_variadic v d r) tl (* The recursive call is correct *)
        | Arrow (Output, v, l, r), hd :: tl ->
            (if was_input && was_data then
               let dy, b' = infer ~was_input ctx hd in
               if b'#is_wrong then (* If the recursive call is wrong, we stop and return bottom *)
                 b#set_wrong b'#get_loc
               else if not ((dy <<= l) ~loc) then
                 (* If preconditions are not satisfied, we stop and return bottom *)
                 b#set_wrong loc);
            Format.eprintf "In output mode for term %a@." ScopedTerm.pretty hd;
            aux (choose_variadic v d r) tl
        | (BVar _ | Any), _ -> (d, new good_call)
        | (Det | Rel | Exp _), _ :: _ ->
            Format.asprintf "deduce: Type error, found dtype %a and arguments %a" pp_dtype d
              (pplist ScopedTerm.pretty ",") tl
            |> anomaly ~loc
      in
      aux d tl
    and infer_app ctx ~loc is_var ty s tl =
      let was_data = is_exp (Compilation.type_ass_2func_mut ~loc env ty) in
      infer_fold ~was_data ~loc ctx (get_dtype ~env ~ctx ~var ~loc ~is_var s) tl
    (* and infer_comma ctx ~loc args d =
       match args with
       | [] -> d
       | ScopedTerm.{ it = Const (_, cut, _); _ } :: xs when F.equal F.cutf cut ->
           infer_comma ctx ~loc xs (Det, new good_call)
       | x :: xs -> infer_comma ctx ~loc xs (infer ctx x) *)
    and infer ~was_input ctx ScopedTerm.({ it; ty; loc } as t) : dtype * good_call =
      Format.eprintf "--> Infer of %a@." ScopedTerm.pretty_ it;
      match it with
      | ScopedTerm.Const b -> infer_app ~was_input ~loc ctx false ty b []
      | Var (b, xs) -> infer_app ~was_input ~loc ctx true ty b xs
      | App (q, { it = Lam (b, _, bo) }, []) when is_quantifier q ->
          infer ~was_input (BVar.add_oname ~loc b (fun x -> Compilation.type_ass_2func_mut ~loc env x) ctx) bo
      (* | App ((Global _, name, _), x, xs) when name = F.andf ->
          Format.eprintf "Calling deduce on a comma separated list of subgoals@.";
          infer_comma ctx ~loc (x :: xs) (Det, new good_call) *)
      | App (b, x, xs) -> infer_app ~was_input ~loc ctx false ty b (x :: xs)
      | Impl (true, c, b) ->
          check_clause ~ctx ~var c |> ignore;
          infer ~was_input ctx b
      | Impl (false, _, _) -> (check_clause ~ctx ~var t, new good_call)
      | Lam (oname, _, c) ->
          begin
            let b = new good_call in
            try
              let _ = check_lam ~ctx ~var t in
              Compilation.type_ass_2func_mut ~loc env ty, b
            with _ -> 
              (* Failure "DetError" -> *)
              b#set_wrong loc;
              Compilation.type_ass_2func_mut ~loc env ty, b
          end
          (* (Compilation.type_ass_2func_mut ~loc env ty, new good_call) *)
          (* Format.eprintf "In lambda of infer, the ty is %a@." (MutableOnce.pp TypeAssignment.pp) ty;
             let dty = Compilation.type_ass_2func_mut ~loc env ty in
             match dty with
             | Arrow (Input, NotVariadic, l, _) ->
                 let ctx = BVar.add_oname ~loc oname (fun _ -> l) ctx in
                 let r, b = infer ~was_input ctx c in
                 (Arrow (Input, NotVariadic, l, r), b)
             | Arrow (Output, NotVariadic, l, _) ->
                 let ctx = BVar.add_oname ~loc oname (fun _ -> Any) ctx in
                 let r, b = infer ~was_input ctx c in
                 Format.eprintf "The output binder is %a@." (Format.pp_print_option pp_dtype) (BVar.get_oname oname ctx);
                 (* let out_det = BVar.get_oname oname ctx |> Option.value ~default:Any in
                    (* if the inferred determinacy of the output does not match the expectation, then b is wrong *)
                    if not ((out_det <<= l) ~loc) then b#set_wrong loc; *)
                 (Arrow (Output, NotVariadic, l, r), b) *)
          (* | Any -> (Any, new good_call)
             | _ -> anomaly ~loc (Format.asprintf "Found lambda term with dtype %a" pp_dtype dty)) *)
      | Discard ->
          Format.eprintf "Calling type_ass_2func_mut in Discard@.";
          (Aux.maximize ~loc @@ Compilation.type_ass_2func_mut ~loc env ty, new good_call)
      | CData _ -> (Exp [], new good_call)
      | Cast (t, _) ->
          let d, good = infer ~was_input ctx t in
          if not good#is_good then raise (FatalDetError("invalid determinacy cast",loc));
          d, good
      | Spill (_, _) -> spill_err ~loc
    in
    let ((det, is_good) as r) = infer ~was_input:false ctx t in
    Format.eprintf "Result of infer for %a is (%a,%s)@." ScopedTerm.pretty t pp_dtype det is_good#show;
    r
  and infer_output ~ctx ~var ScopedTerm.{ it; ty; loc } =
    Format.eprintf "Calling deduce output on %a@." ScopedTerm.pretty_ it;
    let rec aux d args =
      match (d, args) with
      | Arrow (Input, v, _, r), _ :: tl -> aux (choose_variadic v d r) tl
      | Arrow (Output, v, l, r), hd :: tl ->
          let det, is_good = infer ~ctx ~var hd in
          if is_good#is_good && (det <<= l) ~loc then aux (choose_variadic v d r) tl
          else if is_good#is_good then
            raise (DetError(
              Format.asprintf "Invalid determinacy of output term %a.\n Expected: %a\n Found: %a" ScopedTerm.pretty hd
                pp_dtype l pp_dtype det, loc))
          else
            raise (DetError(
              Format.asprintf "The term %a has not the right determinacy (it should be %a)" ScopedTerm.pretty hd
                 pp_dtype l, is_good#get_loc))
      | _ -> ()
    in
    match it with
    | Const _ -> ()
    (* TODO: add case for pi, comma and = *)
    | App (b, x, xs) -> aux (get_dtype ~env ~ctx ~var ~loc ~is_var:false b) (x :: xs)
    | Var (b, xs) -> aux (get_dtype ~env ~ctx ~var ~loc ~is_var:true b) xs
    | _ -> anomaly ~loc @@ Format.asprintf "Invalid term in deduce output %a." ScopedTerm.pretty_ it
  and assume ~ctx ~var d t =
    Format.eprintf "Calling assume on %a@." ScopedTerm.pretty t;
    let var = ref var in
    let add ~loc ~v vname =
      let m = UVar.add ~loc !var vname ~v in
      var := m
    in
    let rec assume_fold ~was_input ~was_data ~loc ctx d (tl : ScopedTerm.t list) =
      match (d, tl) with
      | t, [] -> ()
      | Arrow (Input, v, l, r), h :: tl ->
          assume ~was_input:true ctx l h;
          assume_fold ~was_input ~was_data ~loc ctx (choose_variadic v d r) tl
      | Arrow (Output, v, l, r), h :: tl ->
          if was_input && was_data then assume ~was_input ctx l h;
          assume_fold ~was_input ~was_data ~loc ctx (choose_variadic v d r) tl
      | (BVar _ | Any), _ -> ()
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
         else match t with Scope.Bound b -> BVar.add ctx ~v:d ~loc (name, b) |> ignore | Global g -> ()
       else
         let det_head = get_dtype ~env ~ctx ~var:!var ~loc ~is_var s in
         assume_fold ~was_input ~was_data:(is_exp d) ~loc ctx det_head tl);
      Format.eprintf "The map after call to assume_app is %a@." UVar.pp !var
    and assume ~was_input ctx d ScopedTerm.({ ty; loc; it } as t) : unit =
      Format.eprintf "Assume of %a with dtype %a (was_input:%b)@." ScopedTerm.pretty_ it pp_dtype d was_input;
      match it with
      | App (q, { it = Lam (b, _, bo) }, []) when is_quantifier q ->
          assume ~was_input (BVar.add_oname ~loc b (fun x -> Compilation.type_ass_2func_mut ~loc env x) ctx) d bo
      | Const b -> assume_app ~was_input ctx ~loc ~is_var:false d b []
      | Var (b, tl) -> assume_app ~was_input ctx ~loc ~is_var:true d b tl
      | App (b, hd, tl) -> assume_app ~was_input ctx ~loc ~is_var:false d b (hd :: tl)
      | Discard -> ()
      | Impl (true, h, b) ->
          check_clause ~ctx ~var:!var h |> ignore;
          assume ~was_input ctx d b
      | Impl (false, _H, _B) -> check_clause ~ctx ~var:!var t |> ignore
      | Lam (oname, _, c) -> (
          match d with
          | Arrow (Input, NotVariadic, l, r) ->
              let ctx = BVar.add_oname ~loc oname (fun _ -> l) ctx in
              assume ~was_input ctx r c
          | Arrow (Output, NotVariadic, l, r) ->
              let ctx = BVar.add_oname ~loc oname (fun _ -> l) ctx in
              assume ~was_input ctx r c
          | Any -> ()
          | _ -> anomaly ~loc (Format.asprintf "Found lambda term with dtype %a" pp_dtype d))
      | CData _ -> ()
      | Spill _ -> spill_err ~loc
      | Cast (t, _) -> assume ~was_input ctx d t
    in
    assume ~was_input:false ctx d t;
    !var
  and assume_output ~ctx ~var d tl : UVar.t =
    let rec assume_output d args var =
      match (d, args) with
      | Arrow (Input, v, _, r), _ :: tl -> assume_output (choose_variadic v d r) tl var
      | Arrow (Output, v, l, r), hd :: tl ->
          Format.eprintf "Call assume of %a with dtype:%a@." ScopedTerm.pretty hd pp_dtype l;
          let var = assume ~ctx ~var l hd in
          assume_output (choose_variadic v d r) tl var
      | _ -> var
    in
    assume_output d tl var
  (* returns the updated environment, the dtype of the term and the loc of the term with max dtype *)
  and check ~ctx ~var d t =
    let var = ref var in
    let rec check_app ctx ~loc d ~is_var b tl tm =
      Format.eprintf "-- Entering check_app with term %a@." ScopedTerm.pretty tm;
      let d', is_good = infer ~ctx ~var:!var tm in
      Format.eprintf "-- Checked term dtype is %a and is_good is %s@." pp_dtype d' is_good#show;
      if is_good#is_good then (
        let det = get_dtype ~env ~ctx ~var:!var ~is_var b ~loc in
        Format.eprintf "Assuming output of %a with dtype : %a@." ScopedTerm.pretty tm pp_dtype det;
        var := assume_output ~ctx ~var:!var det tl);
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
          check_clause ~ctx ~var:!var h |> ignore;
          check ~ctx d b
      | Const (Global _, cut, _) when F.equal F.cutf cut -> Det
      (* Cons and nil case may appear in prop position for example in : `f :- [print a, print b, a].` *)
      | App ((Global _, cons, _), x, [ xs ]) when F.equal F.consf cons -> check ~ctx (check ~ctx d x) xs
      | Const (Global _, nil, _) when F.equal F.nilf nil -> d
      | App ((Global _, comma, _), x, xs) when F.equal F.andf comma -> check_comma ctx ~loc d (x :: xs)
      (* smarter than paper, we assume the min of the inference of both. Equivalent
         to elaboration t = s ---> eq1 t s, eq1 s t
         with func eq1 A -> A. *)
      | App ((Global _, name, _), l, [ r ]) when name = F.eqf ->
          let d1, b = infer ~ctx ~var:!var l in
          (if b#is_good then
             let d2, b = infer ~ctx ~var:!var r in
             if b#is_good then (
               Format.eprintf "In equality calling min between the two terms %a and %a@." ScopedTerm.pretty l
                 ScopedTerm.pretty r;
               let m = Aux.min ~loc d1 d2 in
               Format.eprintf "The minimum between %a and %a is %a@." pp_dtype d1 pp_dtype d2 pp_dtype m;
               var := assume ~ctx ~var:!var m l;
               var := assume ~ctx ~var:!var m r));
          d
      (* !! predicate with arity 0 must be checked according to odet: eg

           pred true.
           true.
           true.
           func f.
           f :- true.

          If we look for Warren's functionality, then the example above could
          be accepted since there is no output, and more in general a 0-ary
          predicate cannot unify anything. BUT with implication this is no more
          true:

           pred x.
           func f -> int.
           f Y :- (x :- Y = 3) => (x :- Y = 4) => x.

         but we accept it if ! follows x.
      *)
      | Const b -> check_app ctx ~loc d ~is_var:false b [] t
      | Var (b, xs) -> check_app ctx ~loc d ~is_var:true b xs t
      | App (b, x, xs) -> check_app ctx ~loc d ~is_var:false b (x :: xs) t
      | Cast (b, d') ->
          begin
            try
              let d = check ~ctx d b in
              let d' = Compilation.type_ass_2func_mut ~loc env ty in
              if not ((d <<= d') ~loc) then raise (FatalDetError("illegal determinacy cast",loc));
              d
            with DetError(msg,loc) -> raise (FatalDetError(msg,loc))
          end
      | Spill (b, _) -> spill_err ~loc
      | CData _ -> anomaly ~loc "Found CData in prop position"
      | Lam _ -> anomaly ~loc "Lambda-abstractions are not props"
      | Discard -> anomaly ~loc "Discard found in prop position"
      | Impl (false, hd, tl) -> anomaly ~loc "Found clause in prop position"
    in
    (!var, check ~ctx d t)
  and check_lam ~ctx ~var t : dtype =
    let get_ta n args =
      let ta_sk, _ = F.Map.find n env in
      let ty = TypeAssignment.apply ta_sk args in
      TypeAssignment.create ty
    in
    let otype2term ~loc ty b =
      let ty = TypeAssignment.create ty in
      let it = match b with None -> ScopedTerm.Discard | Some (a, b, c) -> Const (Bound a, b, c) in
      ScopedTerm.{ it; ty; loc }
    in
    let build_clause args ~ctx ~loc ~ty body =
      let new_pred = emit () in
      let args = List.rev args in
      let b = (Scope.Bound elpi_language, new_pred, t.ty) in
      let pred_hd = ScopedTerm.(App (b, List.hd args, List.tl args)) in
      let ctx = BVar.add ~loc ctx (new_pred, elpi_language) ~v:(Compilation.type_ass_2func_mut ~loc env t.ty) in
      let clause = ScopedTerm.{ ty; it = Impl (false, { it = pred_hd; ty; loc }, body); loc } in
      (clause, ctx)
    in
    let add_partial_app (ScopedTerm.{ it; loc } as t) args ty =
      match args with
      | [] -> t
      | hd :: tl -> (
          match it with
          | Const b -> { it = App (b, hd, tl); ty; loc }
          | App (b, x, xs) -> { it = App (b, x, xs @ args); ty; loc }
          | Var (b, xs) -> { it = Var (b, xs @ args); ty; loc }
          | _ -> assert false)
    in
    let rec aux ~ctx ~args ~parial_app (ScopedTerm.{ it; loc; ty } as t) : dtype =
      match (TypeAssignment.deref ty, it) with
      | Prop _, Impl (false, _, bo) ->
          assert (parial_app = []);
          let clause, ctx = build_clause args ~ctx ~loc ~ty bo in
          check_clause ~ctx ~var clause
      | Prop _, _ ->
          let t = add_partial_app t parial_app ty in
          let clause, ctx = build_clause args ~ctx ~loc ~ty t in
          check_clause ~ctx ~var clause
      | Cons b, _ when F.Map.mem b env -> aux ~parial_app ~ctx ~args { t with ty = get_ta b [] }
      | App (b, x, xs), _ when F.Map.mem b env -> aux ~parial_app ~ctx ~args { t with ty = get_ta b (x :: xs) }
      | Cons b, _ -> Exp []
      (* Below: TODO: check that args have the type expected, for example list prop vs list func *)
      | App (b, x, xs), _ -> Exp (List.map (Compilation.type_ass_2func env ~loc) (x :: xs))
      (* If we reach a Uvar | Any case no check is needed, i.e. we don't know  *)
      | ((UVar _ | Any) as t), _ -> Compilation.type_ass_2func env ~loc t
      | Arr (_, _, l, _), Lam (b, _, bo) ->
          aux ~parial_app ~ctx:(BVar.add_oname ~loc b (fun _ -> Any) ctx) ~args:(otype2term ~loc l b :: args) bo
      | Arr (_, Structured.Variadic, _, r), _ ->
          let b = Some (elpi_language, emit (), TypeAssignment.create r) in
          aux ~parial_app ~ctx:(BVar.add_oname ~loc b (fun _ -> Any) ctx) ~args { t with ty = TypeAssignment.create r }
      | Arr (_, _, l, r), _ ->
          (* Partial app: type is Arr but body is not Lam *)
          let b = Some (elpi_language, emit (), TypeAssignment.create l) in
          let nt = otype2term ~loc l b in
          aux ~parial_app:(nt :: parial_app)
            ~ctx:(BVar.add_oname ~loc b (fun _ -> Any) ctx)
            ~args:(nt :: args)
            { t with ty = TypeAssignment.create r }
    in
    aux ~ctx ~args:[] ~parial_app:[] t
  and check_clause ~ctx ~var ScopedTerm.({ it; ty; loc } as t) =
    let ctx = ref (BVar.clone ctx) in
    let var = UVar.clone var in
    let assume_hd b is_var (tm : ScopedTerm.t) =
      (* let _ =
        let do_filter = false in
        let only_check = "" in
        let loc = "test" in
        let _, name, _ = b in
        let bregexp s = Re.Str.regexp (".*" ^ s ^ ".*") in
        if
          do_filter
          && Re.Str.(
               string_match (bregexp only_check) (F.show name) 0 && string_match (bregexp loc) (Loc.show tm.loc) 0)
             |> not
        then raise IGNORE
        (* else assert false *)
      in *)
      let det_hd = get_dtype ~env ~ctx:!ctx ~var ~loc:tm.loc ~is_var b in
      Format.eprintf "Calling assume in hd for terms list %a@." ScopedTerm.pretty tm;
      (det_hd, assume ~ctx:!ctx ~var det_hd tm)
    in
    let rec aux ScopedTerm.{ it; loc; ty } =
      match it with
      | Impl (false, ({ it = Const b } as hd), bo) -> (assume_hd b false hd, hd, Some bo)
      | Impl (false, ({ it = App (b, _, _) } as hd), bo) -> (assume_hd b false hd, hd, Some bo)
      | Const b -> (assume_hd b false t, t, None)
      (* For clauses with quantified unification variables *)
      | App (n, { it = Lam (oname, ty, body) }, []) when is_quantifier n ->
          ctx := BVar.add_oname ~loc oname (Compilation.type_ass_2func_mut ~loc env) !ctx;
          aux body
      | App (b, _, _) -> (assume_hd b false t, t, None)
      | Var (b, _) ->
          warn ~loc (Format.asprintf "cannot load a clause with flex head (found %a)" ScopedTerm.pretty t);
          raise LoadFlexClause
      | _ -> anomaly ~loc @@ Format.asprintf "Found term %a in prop position" ScopedTerm.pretty_ it
    in

    Format.eprintf "=================================================@.";
    Format.eprintf "Checking clause %a at (%a)@." ScopedTerm.pretty t Loc.pp loc;
    Format.eprintf "The var map is %a@." UVar.pp var;
    Format.eprintf "** START CHECKING THE CLAUSE@.";
    let (det_hd, var), hd, body = aux t in
    let var, det_body = Option.(map (check ~ctx:!ctx ~var Det) body |> value ~default:(var, Det)) in
    Format.eprintf "** END CHECKING THE CLAUSE@.";
    Format.eprintf "The var map is %a and det_body is %a@." UVar.pp var pp_dtype det_body;

    let det_pred = get_tl det_hd in
    if not @@ (det_body <<= det_pred) ~loc then
      raise (DetError("expected a functional body, but inferred relational",loc));
    Format.eprintf "** Start checking outputs@.";
    infer_output ~ctx:!ctx ~var hd;
    det_pred
  in
  try (check_clause ~ctx:BVar.empty ~var:UVar.empty t) = Det
  with
  | LoadFlexClause -> false
  | FatalDetError(msg,loc) -> error ~loc ("DetCheck: " ^ msg)
  | DetError(msg,loc) -> error ~loc ("DetCheck: " ^ msg)
