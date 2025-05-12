(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Elpi_util.Util
open Elpi_parser.Ast
open Compiler_data
module C = Constants
module UF = Symbol.UF
module S = Elpi_runtime.Data.Global_symbols

module Format = struct
  include Format

  let eprintf = fun e -> Format.ifprintf Format.err_formatter e
end

let error ~loc msg = error ~loc ("DetCheck: " ^  msg)

type dtype =
  | Det  (** -> for deterministic preds *)
  | Rel  (** -> for relational preds *)
  | Exp of dtype list  (** -> for kinds like list, int, string *)
  | BVar of F.t  (** -> in predicates like: std.exists or in parametric type abbreviations. *)
  | Arrow of Mode.t * Structured.variadic * dtype * dtype  (** -> abstractions *)
  | Any
[@@deriving show, ord]

module Good_call : sig
  (* NOTE:
      For a constructor with a non-polymorphic type, the inferred determinacy of the term
      must match the expected one exactly.
      For a constructor with a polymorphic type, the inferred determinacy of the term
      can differ from the expected one.
      For example, see test90.elpi, test91.elpi, test92.elpi,
      test93.elpi, and test94.elpi.
  *)
  type offending_term = { exp : dtype; found : dtype; term : ScopedTerm.t }
  type t [@@deriving show]

  val init : unit -> t
  val make : exp:dtype -> found:dtype -> ScopedTerm.t -> t
  val is_good : t -> bool
  val is_wrong : t -> bool
  val get : t -> offending_term
  val set : t -> t -> unit
  val set_wrong : t -> exp:dtype -> found:dtype -> ScopedTerm.t -> unit
  val set_good : t -> unit
end = struct
  type offending_term = { exp : dtype; found : dtype; term : ScopedTerm.t }
  type t = offending_term option ref

  let init () : t = ref None
  let make ~exp ~found term : t = ref @@ Some { exp; found; term }
  let is_good (x : t) = Option.is_none !x
  let is_wrong (x : t) = Option.is_some !x
  let get (x : t) = Option.get !x
  let set (t1 : t) (t2 : t) = t1 := !t2
  let set_wrong (t1 : t) ~exp ~found term = t1 := Some { exp; found; term }
  let set_good t = t := None
  let show (x : t) = match !x with None -> "true" | Some e -> Format.asprintf "false (%a)" Loc.pp e.term.loc
  let pp fmt x = Format.fprintf fmt "%s" (show x)
end

exception DetError of (Scope.t ScopedTerm.ty_name option * Good_call.t)
exception FatalDetError of (Scope.t ScopedTerm.ty_name option * Good_call.t)
exception RelationalBody of (Scope.t ScopedTerm.ty_name option * Good_call.t)
exception CastError of (Scope.t ScopedTerm.ty_name option * Good_call.t)
exception KError of (Scope.t ScopedTerm.ty_name option * Good_call.t)
exception LoadFlexClause of ScopedTerm.t

let rec pp_dtype fmt = function
  | Det -> Format.fprintf fmt "Det"
  | Rel -> Format.fprintf fmt "Rel"
  | BVar b -> Format.fprintf fmt "BVar %a" F.pp b
  | Any -> Format.fprintf fmt "Any"
  | Arrow (m, Variadic, l, r) -> Format.fprintf fmt "(Variadic %a %a-> %a)" pp_dtype l Mode.pretty m pp_dtype r
  | Arrow (m, _, l, r) -> Format.fprintf fmt "(%a %a-> %a)" pp_dtype l Mode.pretty m pp_dtype r
  | Exp l -> Format.fprintf fmt "Exp [%a]" (pplist pp_dtype ", ") l

type t = (TypeAssignment.skema * Loc.t) F.Map.t [@@deriving show, ord]

let arr m ~v a b = Arrow (m, v, a, b)
let is_exp = function Exp _ -> true | _ -> false
let choose_variadic v full right = if v = Structured.Variadic then full else right

module Compilation = struct

  let type_ass_2func ~loc (env : t) t : dtype =
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
          type_ass_2func ~loc (Arr (MutableOnce.get m, v, l, r))
      (*
          The typical example for the following case is a predicate quantified by a pi,
          an example can be found in tests/sources/findall.elpi
      *)
      | Arr (MRef _, v, l, r) -> arr ~v Output (type_ass_2func ~loc l) (type_ass_2func ~loc r)
      | UVar a -> if MutableOnce.is_set a then (type_ass_2func ~loc (TypeAssignment.deref a)) else BVar (MutableOnce.get_name a)
    in
    type_ass_2func ~loc t

  let type_ass_2func_mut ~loc (env : t) t = type_ass_2func ~loc env (TypeAssignment.deref t)
end

module Aux = struct
  let check_variadic f1 f2 mode d1 v1 l1 r1 d2 v2 l2 r2 =
    match (v1, v2) with
    | Structured.(Variadic, Variadic) -> Arrow (mode, v1, f1 l1 l2, f2 r1 r2)
    | NotVariadic, NotVariadic -> Arrow (mode, v1, f1 l1 l2, f2 r1 r2)
    | Variadic, NotVariadic -> Arrow (mode, v1, f1 l1 l2, f2 d1 r2)
    | NotVariadic, Variadic -> Arrow (mode, v1, f1 l1 l2, f2 r1 d2)

  let (<=) m1 m2 ~positive ~d1 ~d2 =
    let open Mode in
    match m1, m2 with
    | Input, Input -> Input, not positive, (d2, d1)
    | Output, Input -> (if positive then Output else Input), not positive, (if positive then d2,d1 else d1,d2)
    | Output, Output -> Output, positive, (d1, d2)
    | Input, Output -> (if not positive then Output else Input), positive, (if positive then d1,d2 else d2,d1)
  
  let rec min_max ~positive ~loc ~d1 ~d2 f1 f2 =
    if f1 = d1 || f2 = d1 then d1
    else
      match (f1, f2) with
      | Det, Det -> Det
      | Rel, Rel -> Rel
      | a, (Any | BVar _) | (Any | BVar _), a -> a
      | Exp [ ((Det | Rel | Exp _) as x) ], (Det | Rel) -> min_max ~positive ~loc ~d1 ~d2 x f2
      | (Det | Rel), Exp [ ((Det | Rel | Exp _) as x) ] -> min_max ~positive ~loc ~d1 ~d2 f1 x
      | Exp l1, Exp l2 -> (
          try Exp (List.map2 (min_max ~positive ~loc ~d1 ~d2) l1 l2)
          with Invalid_argument _ -> error ~loc (Format.asprintf "min_max invalid exp_length: %a != %a" pp_dtype f1 pp_dtype f2))
      (* | Arrow (m1, _, _, _), Arrow (m2, _, _, _) when m1 <> m2 -> error ~loc "Mode mismatch" *)
      | Arrow (m1, v1, l1, r1), Arrow (m2, v2, l2, r2) ->
          let m, negative, (d1', d2') = (m1 <= m2) ~positive ~d1 ~d2 in
          check_variadic (min_max ~positive:negative ~loc ~d1:d1' ~d2:d2') (min_max ~positive ~loc ~d1 ~d2) m f1 v1 l1 r1 f2 v2 l2 r2
      (* | Arrow (Output, v1, l1, r1), Arrow (_, v2, l2, r2) ->
          check_variadic (min_max ~positive ~loc ~d1 ~d2) (min_max ~positive ~loc ~d1 ~d2) Output f1 v1 l1 r1 f2 v2 l2 r2 *)
      | Arrow (_, Variadic, _, r), f2 -> min_max ~positive ~loc ~d1 ~d2 r f2
      | f2, Arrow (_, Variadic, _, r) -> min_max ~positive ~loc ~d1 ~d2 r f2
      | _ -> Format.asprintf "min between %a and %a" pp_dtype f1 pp_dtype f2 |> error ~loc

  let min = min_max ~positive:true ~d1:Det ~d2:Rel
  let max = min_max ~positive:true ~d1:Rel ~d2:Det

  let rec minimize_maximize ~loc ~d1 ~d2 d =
    match d with
    | Det | Rel -> d1
    | Exp l -> Exp (List.map (minimize_maximize ~loc ~d1 ~d2) l)
    | Arrow (Input, v, l, r) ->
        Arrow (Input, v, minimize_maximize ~loc ~d1:d2 ~d2:d1 l, minimize_maximize ~loc ~d1 ~d2 r)
    | Arrow (Output, v, l, r) -> Arrow (Output, v, minimize_maximize ~loc ~d1 ~d2 l, minimize_maximize ~loc ~d1 ~d2 r)
    | Any -> Any
    | BVar b -> BVar b

  (* let minimize = minimize_maximize ~d1:Det ~d2:Rel *)
  let maximize = minimize_maximize ~d1:Rel ~d2:Det

  let is_maximized ~loc d = d = maximize ~loc d

  let wrong_type ~loc a b =
    error ~loc @@ Format.asprintf "Typing invariant broken: %a <<= %a\n%!" pp_dtype a pp_dtype b

  let wrong_bvars ~loc v1 v2 =
    error ~loc @@ Format.asprintf "<<=: TC did not unify two unif vars (%a and %a)" F.pp v1 F.pp v2

  let ( <<= ) ~loc a b =
    let rec choose_dir ~loc t1 t2 = function Mode.Input -> aux ~loc t2 t1 | Mode.Output -> aux ~loc t1 t2
    and aux ~loc a b =
      match (a, b) with
      | _, Any -> true
      | Any, _ -> b = maximize ~loc b (* TC may accept A = any, so we do too *)
      | BVar v1, BVar v2 -> F.equal v1 v2 || wrong_bvars ~loc v1 v2
      | BVar _, _ | _, BVar _ -> wrong_type ~loc a b
      | Exp l1, Exp l2 -> ( try List.for_all2 (aux ~loc) l1 l2 with Invalid_argument _ -> wrong_type ~loc a b)
      | Exp [ ((Det | Rel | Exp _) as x) ], (Det | Rel) -> aux ~loc x b
      | (Det | Rel), Exp [ ((Det | Rel | Exp _) as x) ] -> aux ~loc a x
      | Arrow (m1, NotVariadic, l1, r1), Arrow (_, NotVariadic, l2, r2) -> choose_dir ~loc l1 l2 m1 && aux r1 r2 ~loc
      | Arrow (m1, NotVariadic, l1, r1), Arrow (_, Variadic, l2, _) -> choose_dir ~loc l1 l2 m1 && aux r1 b ~loc
      | Arrow (m1, Variadic, l1, _), Arrow (_, NotVariadic, l2, r2) -> choose_dir ~loc l1 l2 m1 && aux a r2 ~loc
      | Arrow (m1, Variadic, l1, r1), Arrow (_, Variadic, l2, r2) -> choose_dir ~loc l1 l2 m1 && aux r1 r2 ~loc
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

(* 
  Module for mapping variable names to their determinacy.
  When a variable is added to the map and it already exists,
  its dtype is updated to the minimum value between the
  old and the new value.
*)
module EnvMaker (M : Map.S) : sig
  type t [@@deriving show]

  val add : new_:bool -> loc:Loc.t -> v:dtype -> t -> M.key -> t
  val get : t -> M.key -> dtype option
  val clone : t -> t
  val empty : t
  val iter : (M.key -> dtype -> unit) -> t -> unit
end = struct
  type t = dtype ref M.t [@@deriving show]

  let add ~new_ ~loc ~(v : dtype) (env : t) (n : M.key) : t =
    if new_ then M.add n (ref v) env 
    else match M.find_opt n env with
    | None -> M.add n (ref v) env
    | Some v' ->
        v' := Aux.min ~loc v !v';
        env

  let get (env : t) (k : M.key) = Option.map ( ! ) (M.find_opt k env)
  let empty = M.empty
  let clone : t -> t = M.map (fun v -> ref !v)

  let iter f (t:t) = M.iter (fun k v -> f k !v) t
end

module Uvar = EnvMaker (F.Map)

module BVar = struct
  include EnvMaker (Scope.Map)

  let add_oname ~new_ ~loc oname f ctx =
    Format.eprintf "add_oname: %a@." (Format.pp_print_option (fun fmt (s,n,tya) -> 
      Format.fprintf fmt "@[<hov 2>%a@ with tya:@ %a@ and compiled@ %a@ -- [old: %a])]" F.pp n (TypeAssignment.pretty_mut_once) (TypeAssignment.deref tya)
      pp_dtype (f tya)
      (Format.pp_print_option pp_dtype) (get ctx (n,s))
      )) oname;
    match oname with None -> ctx | Some (scope, name, tya) -> add ~new_ ~loc ctx (name, scope) ~v:(f tya)
end

let get_dtype ~env ~ctx ~var ~loc ~is_var (t, name, tya)=
  let get_ctx = function
    | None -> error ~loc (Format.asprintf "DetCheck: Bound var %a should be in the local map" F.pp name)
    | Some e -> e
  in
  let get_var = function None -> Aux.maximize ~loc (Compilation.type_ass_2func_mut ~loc env tya) | Some e -> e in
  let get_con _x = Compilation.type_ass_2func_mut ~loc env tya in
  let det_head =
    if is_var then get_var @@ Uvar.get var name
    else match t with Scope.Bound b -> get_ctx @@ BVar.get ctx (name, b) | Global g -> get_con g.resolved_to
  in
  Format.eprintf "Type of %a is %a@." F.pp name pp_dtype det_head;
  (* Format.eprintf "The functionality of %a is %a (its type is %a)@ Full type is %a@." F.pp name pp_dtype det_head
    TypeAssignment.pretty_mut_once_raw (TypeAssignment.deref tya) (MutableOnce.pp (TypeAssignment.pp) ) tya; *)
  det_head

let spill_err ~loc = anomaly ~loc "Everything should have already been spilled"

let check_clause ~type_abbrevs:ta ~types ~unknown (t : ScopedTerm.t) : unit =
  let same_symb symb symb' =
    match symb' with
    | Scope.Global { resolved_to = x } ->
        begin match SymbolResolver.resolved_to types x with
        | Some symb' -> TypingEnv.same_symbol types symb symb'
        | _ -> false
        end
    | _ -> false
  in
  let get_user_type ~loc (s,_,_) = match s with
    | Scope.Global {resolved_to = x } ->
      let open TypeAssignment in
      let rec mk_args = function Ty t -> [] | Lam (_, b) -> Any :: mk_args b in
      let apply ty = TypeAssignment.apply ty (mk_args ty) in
      let compile TypingEnv.{ty} = Compilation.type_ass_2func ~loc ta (apply ty) in
      let to_dtype x = Option.map compile @@ TypingEnv.resolve_symbol_opt x types in
      Option.bind (SymbolResolver.resolved_to types x) to_dtype
    | Bound _ -> None
  in
  let has_undeclared_signature (b, f, _) =
    match F.Map.find_opt f unknown with Some (_, symb) -> same_symb symb b | _ -> false
  in
  let is_global (b, _, _) name = same_symb name b in
  let is_quantifier x = is_global x S.pi || is_global x S.sigma in
  let undecl_disclaimer = function
    | Some pred_name when has_undeclared_signature pred_name ->
        let snd (_, x, _) = x in
        let trd (_, _, x) = x in
        Format.asprintf
          "@[<hov 2>Predicate %a has no declared signature,@ providing one could fix the following error@ (inferred \
           signature: %a)@]@\n\
           DetCheck: " F.pp (snd pred_name) TypeAssignment.pretty_mut_once
          (TypeAssignment.deref @@ trd pred_name)
    | _ -> ""
  in

  let cnt = ref 0 in
  let emit () =
    incr cnt;
    F.from_string ("*dummy" ^ string_of_int !cnt)
  in
  let rec get_tl = function Arrow (_, _, _, r) -> get_tl r | e -> e in

  let is_cut ScopedTerm.{ it } = match it with Const b -> is_global b S.cut | _ -> false in

  let rec infer ~ctx ~var t : dtype * Good_call.t =
    let rec infer_fold ~was_input ~was_data ~loc ~user_dtype ctx d hd tl =
      Format.eprintf "Starting infer fold at %a with dtype:@[%a@] and user_dtype:@[%a@]@." Loc.pp loc pp_dtype d (Format.pp_print_option pp_dtype) user_dtype;
      let b = Good_call.init () in
      let split_user_dtype = function
        | None -> Any, None
        | Some Any -> Any, None
        | Some (Arrow (m,_,l,r)) -> l, Some r 
        | Some d -> error ~loc  @@ Format.asprintf "DetCheck: found dtype:%a" pp_dtype d
      in
      let rec aux ~user_dtype d tl : (dtype * Good_call.t) =
        Format.eprintf "@[<hov 2>In recursive call for infer.aux with head-term@ @[%a@], good_call is %a -- and dtype@ @[%a@] and user_dytpe is @[%a@]@]@." (Format.pp_print_option ScopedTerm.pretty) (List.nth_opt tl 0)
          Good_call.pp b pp_dtype d (Format.pp_print_option pp_dtype) user_dtype;
        match (d, tl) with
        | Arrow (_, Variadic, _, t), [] -> (t, b)
        | t, [] -> (t, b)
        | Arrow (Input, v, l, r), h :: tl ->
            let l_user, r_user = split_user_dtype user_dtype in
            let loc = h.loc in
            let dy, b' = infer ~was_input:true ctx h in
            Format.eprintf "infer.aux in Input branch with dtype:%a and t:%a@." pp_dtype l ScopedTerm.pretty h;
            Format.eprintf "end infer.aux for term %a with b':%a and not ((dy <<= l) ~loc):%b and was_data:%b@." ScopedTerm.pretty h Good_call.pp b' (not ((dy <<= l) ~loc)) was_data;          
            if Good_call.is_wrong b' then begin
              let max_exp = Aux.maximize ~loc dy in
              if not ((max_exp <<= l_user) ~loc) then raise (KError (Some hd, b'))
              else if not ((max_exp <<= l) ~loc) then Good_call.set b b'
            end 
            else if not ((dy <<= l_user) ~loc) then
              raise (KError (Some hd, (Good_call.set_wrong b ~exp:l_user ~found:dy h; b)))
            else if not ((dy <<= l) ~loc) then (
              (* If preconditions are not satisfied, we stop and return bottom *)
              Good_call.set_wrong b ~exp:l ~found:dy h;
              Format.eprintf "Invalid determinacy set b to wrong (%a)@." Good_call.pp b);
            if Good_call.is_wrong b then Any, b 
            else aux ~user_dtype:(choose_variadic v user_dtype r_user) (choose_variadic v d r) tl
        | Arrow (Output, v, l, r), hd :: tl ->
            if was_data then
              aux ~user_dtype (Arrow (Input, v, l, r)) (hd :: tl)
            else
              let l_user, r_user = split_user_dtype user_dtype in
              aux ~user_dtype:(choose_variadic v user_dtype r_user) (choose_variadic v d r) tl
        | (BVar _ | Any), _ -> (d, Good_call.init ())
        | (Det | Rel | Exp _), _ :: _ ->
            Format.asprintf "deduce: Type error, found dtype %a and arguments %a" pp_dtype d
              (pplist ScopedTerm.pretty ",") tl
            |> anomaly ~loc
      in
      aux ~user_dtype d tl
    and infer_app ctx ~loc is_var ty s tl =
      let was_data = is_exp (Compilation.type_ass_2func_mut ~loc ta ty) in
      let user_dtype = if was_data then get_user_type ~loc s else None in
      Format.eprintf "Is_exp: %b@." was_data;
      let dtype = get_dtype ~env:ta ~ctx ~var ~loc ~is_var s in
      infer_fold ~was_data ~user_dtype ~loc ctx dtype s tl
    and infer_and ~was_input ctx ~loc args (_, r as dr) =
       match args with
       | [] -> dr
       | x :: xs when is_cut x -> 
        Good_call.set_good r;
        infer_and ~was_input ctx ~loc xs (Det, r)
       | x :: xs ->
        let dr' = infer ~was_input ctx x in
        if fst dr' = Rel then infer_and ~was_input ctx ~loc xs dr'
        else infer_and ~was_input ctx ~loc xs dr
    and infer ~was_input ctx ScopedTerm.({ it; ty; loc } as t) : dtype * Good_call.t =
      Format.eprintf "--> Infer of @[%a@]@." ScopedTerm.pretty_ it;
      match it with
      | ScopedTerm.Const b -> infer_app ~was_input ~loc ctx false ty b []
      | Var (b, xs) -> infer_app ~was_input ~loc ctx true ty b xs
      | App (q, { it = Lam (b, _, bo) }, []) when is_quantifier q ->
        (* Format.eprintf "%a@." ScopedTerm.pp bo; *)
          infer ~was_input (BVar.add_oname ~new_:false ~loc b (fun x -> Compilation.type_ass_2func_mut ~loc ta x) ctx) bo
      | App (g, x, xs) when is_global g S.and_ ->
          Format.eprintf "Calling deduce on a comma separated list of subgoals@.";
          infer_and ~was_input ctx ~loc (x :: xs) (Det, Good_call.init ())
      | App (b, x, xs) -> infer_app ~was_input ~loc ctx false ty b (x :: xs)
      | Impl (L2R, c, b) ->
          check_clause ~ctx ~var c |> ignore;
          infer ~was_input ctx b
      | Impl (L2RBang, c, b) ->
          check_clause ~ctx ~var ~has_tail_cut:true c |> ignore;
          infer ~was_input ctx b
      | Impl (R2L, _, _) -> 
        Format.eprintf "Recursive call to check clause@.";
        (check_clause ~ctx ~var t, Good_call.init ())
      | Lam _ -> (
          try
            let _ = check_lam ~ctx ~var t in
            (Compilation.type_ass_2func_mut ~loc ta ty, Good_call.init ())
          with FatalDetError (_,b1) | DetError (_, b1) | RelationalBody (_, b1) -> (Compilation.type_ass_2func_mut ~loc ta ty, b1))
      | Discard ->
          Format.eprintf "Calling type_ass_2func_mut in Discard@.";
          (Compilation.type_ass_2func_mut ~loc ta ty, Good_call.init ())
      | CData _ -> (Exp [], Good_call.init ())
      | Cast (t, _) ->
          let d, good = infer ~was_input ctx t in
          if Good_call.is_wrong good then raise (FatalDetError (None, good));
          (d, good)
      | Spill (_, _) -> spill_err ~loc
    in
    let ((det, gc) as r) = infer ~was_input:false ctx t in
    Format.eprintf "Result of infer for %a is (%a,%a)@." ScopedTerm.pretty t pp_dtype det Good_call.pp gc;
    r
  and infer_output ~pred_name ~ctx ~var ScopedTerm.{ it; loc } =
    Format.eprintf "Calling deduce output on %a@." ScopedTerm.pretty_ it;
    let rec aux d args =
      match (d, args) with
      | Arrow (Input, v, _, r), _ :: tl -> aux (choose_variadic v d r) tl
      | Arrow (Output, v, l, r), hd :: tl ->

          let det, gc = infer ~ctx ~var hd in
          Format.eprintf "Inference of %a gives (%a,%a)@." ScopedTerm.pretty hd pp_dtype det Good_call.pp gc;

          if Good_call.is_wrong gc && Aux.is_maximized ~loc l then aux (choose_variadic v d r) tl
          else if Good_call.is_good gc && (det <<= l) ~loc then aux (choose_variadic v d r) tl
          else if Good_call.is_good gc then raise (DetError (Some pred_name, Good_call.make ~exp:l ~found:det hd))
          else raise (DetError (Some pred_name, gc))
      | _ -> ()
    in
    match it with
    | Const _ -> ()
    (* TODO: add case for pi, comma and = *)
    | App (b, x, xs) -> aux (get_dtype ~env:ta ~ctx ~var ~loc ~is_var:false b) (x :: xs)
    | Var (b, xs) -> aux (get_dtype ~env:ta ~ctx ~var ~loc ~is_var:true b) xs
    | _ -> anomaly ~loc @@ Format.asprintf "Invalid term in deduce output %a." ScopedTerm.pretty_ it
  and assume ?(was_input=false) ~ctx ~var d t =
    Format.eprintf "Calling assume on %a with det : %a@." ScopedTerm.pretty t pp_dtype d;
    let var = ref var in
    let add ~loc ~v vname =
      Format.eprintf "Permanently adding %a : %a@." F.pp vname pp_dtype v;
      let m = Uvar.add ~new_:false ~loc !var vname ~v in
      var := m
    in
    let rec assume_fold ~was_input ~was_data ~loc ctx d (tl : ScopedTerm.t list) : unit =
      match (d, tl) with
      | _, [] -> ()
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
    and assume_app ~was_input ctx ~loc d ((t, name, _) as s) tl =
      Format.eprintf "Calling assume_app on: %a with dtype %a with args [%a] and@." F.pp name pp_dtype d
        (pplist ~boxed:true ScopedTerm.pretty " ; ")
        tl;
      match t with 
      | Scope.Bound b -> assume_var ~is_var:(Some b) ~ctx ~loc d s tl
      | _ ->
         let det_head = get_dtype ~env:ta ~ctx ~var:!var ~loc ~is_var:false s in
         assume_fold ~was_input ~was_data:(is_exp d) ~loc ctx det_head tl;
      Format.eprintf "The map after call to assume_app is %a@." Uvar.pp !var
    and assume_var ~is_var ~ctx ~loc d ((_,name,_) as s) tl =
      let rec replace_signature_tgt ~with_ d' = function 
      | [] -> with_
      | _::xs -> match d' with
        | Arrow (_, Variadic, _, _) -> replace_signature_tgt ~with_ d' xs
        | Arrow (m, NotVariadic, l, r) ->  Arrow (m, NotVariadic, l, replace_signature_tgt ~with_ r xs)
        | _ -> error ~loc @@ Format.asprintf "replace_signature_tgt: Type error: found %a " pp_dtype d'  in
      let dtype = get_dtype ~env:ta ~ctx ~var:!var ~loc ~is_var:(is_var = None) s in
      Format.eprintf "Dtype of %a is %a@." F.pp name pp_dtype dtype;
      let d' = replace_signature_tgt dtype tl  ~with_:d in
      Format.eprintf "d' is %a@." pp_dtype d';
      match is_var with
      | None -> add ~loc ~v:d' name
      | Some b -> BVar.add ~new_:false ctx ~v:d' ~loc (name, b) |> ignore
    and assume ~was_input ctx d ScopedTerm.({ loc; it }) : unit =
      Format.eprintf "Assume of %a with dtype %a (was_input:%b)@." ScopedTerm.pretty_ it pp_dtype d was_input;
      match it with
      | App (q, { it = Lam (b, _, bo) }, []) when is_quantifier q ->
          assume ~was_input (BVar.add_oname ~new_:false ~loc b (fun x -> Compilation.type_ass_2func_mut ~loc ta x) ctx) d bo
      | Const b -> assume_app ~was_input ctx ~loc d b []
      | Var (b, tl) -> assume_var ~loc ~ctx ~is_var:None d b tl
      | App (b, hd, tl) -> assume_app ~was_input ctx ~loc d b (hd :: tl)
      | Discard -> ()
      | Impl (L2R, h, b) ->
          check_clause ~ctx ~var:!var h |> ignore;
          assume ~was_input ctx d b
      | Impl (L2RBang, h, b) ->
        check_clause ~ctx ~var:!var ~has_tail_cut:true h |> ignore;
        assume ~was_input ctx d b
      | Impl (R2L, ({it = Const b} as t), bo) -> 
        let dtype, var' = assume_hd ~is_var:false ~loc ~ctx ~var:!var b t [] in
        assume ~was_input:false ctx (get_tl dtype) bo
      | Impl (R2L, {it = App (b, x, xs)}, bo) -> 
        let dtype, var' = assume_hd ~is_var:false ~loc ~ctx ~var:!var b t (x::xs) in
        Uvar.iter (fun k v -> add ~loc ~v k) var';
        assume ~was_input:false ctx (get_tl dtype) bo
      | Impl (R2L, _, _B) -> ()
      | Lam (oname, _, c) -> (
          match d with
          | Arrow (Input, NotVariadic, l, r) ->
              let ctx = BVar.add_oname ~new_:true ~loc oname (fun _ -> l) ctx in
              assume ~was_input ctx r c
          | Arrow (Output, NotVariadic, l, r) ->
              let ctx = BVar.add_oname ~new_:true ~loc oname (fun _ -> l) ctx in
              assume ~was_input ctx r c
          | Any -> ()
          | _ -> anomaly ~loc (Format.asprintf "Found lambda term with dtype %a" pp_dtype d))
      | CData _ -> ()
      | Spill _ -> spill_err ~loc
      | Cast (t, _) -> assume ~was_input ctx d t
    in
    assume ~was_input ctx d t;
    !var
  and assume_output ~ctx ~var d tl : Uvar.t =
    let rec assume_output d args var =
      match (d, args) with
      | Arrow (Input, v, _, r), _ :: tl -> assume_output (choose_variadic v d r) tl var
      | Arrow (Output, v, l, r), hd :: tl ->
          Format.eprintf "Call assume of %a with dtype:%a@." ScopedTerm.pretty hd pp_dtype l;
          let var = assume ~was_input:true ~ctx ~var l hd in
          assume_output (choose_variadic v d r) tl var
      | _ -> var
    in
    assume_output d tl var
  and assume_input ~ctx ~var d tl : Uvar.t =
    let rec assume_input d args var =
      match (d, args) with
      | Arrow (Input, v, l, r), hd :: tl ->
        Format.eprintf "Call assume of %a with dtype:%a@." ScopedTerm.pretty hd pp_dtype l;
          let var = assume ~was_input:true ~ctx ~var l hd in
          assume_input (choose_variadic v d r) tl var
      | Arrow (Output, v, _, r), _ :: tl ->assume_input (choose_variadic v d r) tl var
      | _ -> var
    in
    assume_input d tl var
  (* returns the updated environment, the dtype of the term and if it has a top level cut *)
  and check ~ctx ~var (d : dtype) t : Uvar.t * (dtype * _) * bool =
    let has_top_level_cut = ref false in
    let var = ref var in
    let rec check_app ctx ~loc (d : dtype) ~is_var b tl tm =
      Format.eprintf "@[<hov 2>-- Entering check_app with term@ @[%a@]@]@." ScopedTerm.pretty tm;
      let d', gc = infer ~ctx ~var:!var tm in
      Format.eprintf "-- Checked term dtype is %a and gc is %a@." pp_dtype d' Good_call.pp gc;
      if Good_call.is_good gc then (
        let det = get_dtype ~env:ta ~ctx ~var:!var ~is_var b ~loc in
        Format.eprintf "Assuming output of %a with dtype : %a@." ScopedTerm.pretty tm pp_dtype det;
        var := assume_output ~ctx ~var:!var det tl);
      Format.eprintf "In check_app before result, comparing %a with %a (expected %a)@."
        ScopedTerm.pretty tm pp_dtype d' pp_dtype d;
      if Good_call.is_good gc && (d' <<= d) ~loc then (Aux.max ~loc (get_tl d) (get_tl d'), tm) else (Rel, tm)
    and check_comma ctx ~loc (d, bad_atom) args =
      match args with
      | [] -> (d, bad_atom)
      | x :: xs ->
          Format.eprintf "Checking comma with first term %a@." ScopedTerm.pretty x;
          let d1, bad_atom1 = check ~ctx d x in
          (* we save the loc of the last offending atom *)
          let bad_atom = if d1 = Rel && d = Det then bad_atom1 else bad_atom in
          Format.eprintf "Loc:%a --> Badatom is %a@." Loc.pp bad_atom.loc ScopedTerm.pretty bad_atom;
          check_comma ctx ~loc (d1, bad_atom) xs
    and check ~ctx (d : dtype) ScopedTerm.({ it; loc } as t) : dtype * ScopedTerm.t =
      match it with
      | Impl (L2R, h, b) ->
          check_clause ~ctx ~var:!var h |> ignore;
          check ~ctx d b
      | Impl (L2RBang, h, b) ->
        check_clause ~ctx ~var:!var ~has_tail_cut:true h |> ignore;
        check ~ctx d b
      | Const b when is_global b S.cut -> (Det, t)
      | App (q, { it = Lam (b, _, bo) }, []) when is_quantifier q ->
          check ~ctx:(BVar.add_oname ~new_:true ~loc b (Compilation.type_ass_2func_mut ~loc ta) ctx) d bo
      (* Cons and nil case may appear in prop position for example in : `f :- [print a, print b, a].` *)
      | App (b, x, [ xs ]) when is_global b S.cons -> check ~ctx (check ~ctx d x |> fst) xs
      | Const b when is_global b S.nil -> (d, t)
      | App (b, x, xs) when is_global b S.and_ -> check_comma ctx ~loc (d, t) (x :: xs)
      (* smarter than paper, we assume the min of the inference of both. Equivalent
         to elaboration t = s ---> eq1 t s, eq1 s t
         with func eq1 A -> A. *)
      | App (b, l, [ r ]) when is_global b S.eq ->
          let d1, gc = infer ~ctx ~var:!var l in
          (if Good_call.is_good gc then
             let d2, gc = infer ~ctx ~var:!var r in
             if Good_call.is_good gc then (
               Format.eprintf "In equality calling min between the two terms %a and %a@." ScopedTerm.pretty l
                 ScopedTerm.pretty r;
               let m = Aux.min ~loc d1 d2 in
               Format.eprintf "The minimum between %a and %a is %a@." pp_dtype d1 pp_dtype d2 pp_dtype m;
               var := assume ~ctx ~var:!var m l;
               var := assume ~ctx ~var:!var m r));
          (d, t)
      (* Const are checked due to test68.elpi and test69.elpi *)
      | Const b -> check_app ctx ~loc d ~is_var:false b [] t
      | Var (b, xs) -> check_app ctx ~loc d ~is_var:true b xs t
      | App (b, x, xs) -> check_app ctx ~loc d ~is_var:false b (x :: xs) t
      | Cast (b, _) -> (
          try
            let d, _ = check ~ctx d b in
            let d' = Compilation.type_ass_2func_mut ~loc ta b.ty in
            if not ((d <<= d') ~loc) then raise (CastError (None, Good_call.make ~exp:d' ~found:d b));
            (d, t)
          with DetError x -> raise (FatalDetError x))
      | Spill _ -> spill_err ~loc
      | CData _ -> anomaly ~loc "Found CData in prop position"
      | Lam _ -> anomaly ~loc "Lambda-abstractions are not props"
      | Discard -> anomaly ~loc "Discard found in prop position"
      | Impl (R2L, _, _) -> anomaly ~loc "Found clause in prop position"
    in
    (!var, check ~ctx d t, !has_top_level_cut)
  and check_lam ~ctx ~var t : dtype =
    Format.eprintf "check_lam: t = %a@." ScopedTerm.pretty t;
    let get_ta n args =
      let ta_sk, _ = F.Map.find n ta in
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
      let b = (Scope.Global {resolved_to=SymbolResolver.make ();escape_ns=false}, new_pred, t.ty) in
      let pred_hd = ScopedTerm.(App (b, List.hd args, List.tl args)) in
      (* let ctx = BVar.add ~loc ctx (new_pred, elpi_language) ~v:(Compilation.type_ass_2func_mut ~loc env t.ty) in *)
      let clause = ScopedTerm.{ ty; it = Impl (R2L, { it = pred_hd; ty; loc }, body); loc } in
      Format.eprintf "Clause is %a@." ScopedTerm.pretty clause;
      (clause, ctx)
    in
    let add_partial_app (ScopedTerm.{ it; loc } as t) args ty =
      let args = List.rev args in
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
      | Prop _, Impl (R2L, _, bo) ->
          assert (parial_app = []);
          let clause, ctx = build_clause args ~ctx ~loc ~ty bo in
          check_clause ~ctx ~var clause
      | Prop _, _ ->
          let t = add_partial_app t parial_app ty in
          let clause, ctx = build_clause args ~ctx ~loc ~ty t in
          Format.eprintf "check_lam: built clause is = %a@." ScopedTerm.pretty clause;
          check_clause ~ctx ~var clause
      | Cons b, _ when F.Map.mem b ta -> aux ~parial_app ~ctx ~args { t with ty = get_ta b [] }
      | App (b, x, xs), _ when F.Map.mem b ta -> aux ~parial_app ~ctx ~args { t with ty = get_ta b (x :: xs) }
      | Cons _, _ -> Exp []
      (* Below: TODO: check that args have the type expected, for example list prop vs list func *)
      | App (_, x, xs), _ -> Exp (List.map (Compilation.type_ass_2func ta ~loc) (x :: xs))
      (* If we reach a Uvar | Any case no check is needed, i.e. we don't know  *)
      | ((UVar _ | Any) as t), _ -> Compilation.type_ass_2func ta ~loc t
      | Arr (_, _, l, _), Lam (b, _, bo) ->
          aux ~parial_app ~ctx:(BVar.add_oname ~new_:true ~loc b (fun t -> Aux.maximize ~loc (Compilation.type_ass_2func_mut ~loc ta t)) ctx) ~args:(otype2term ~loc l b :: args) bo
      | Arr (_, Structured.Variadic, _, r), _ ->
          let b = Some (elpi_language, emit (), TypeAssignment.create r) in
          aux ~parial_app ~ctx:(BVar.add_oname ~new_:true ~loc b (fun t -> Aux.maximize ~loc (Compilation.type_ass_2func_mut ~loc ta t)) ctx) ~args { t with ty = TypeAssignment.create r }
      | Arr (_, _, l, r), _ ->
          (* Partial app: type is Arr but body is not Lam *)
          let b = Some (elpi_language, emit (), TypeAssignment.create l) in
          let nt = otype2term ~loc l b in
          aux ~parial_app:(nt :: parial_app)
            ~ctx:(BVar.add_oname ~new_:true ~loc b (fun t -> Aux.maximize ~loc (Compilation.type_ass_2func_mut ~loc ta t)) ctx)
            ~args:(nt :: args)
            { t with ty = TypeAssignment.create r }
    in
    aux ~ctx ~args:[] ~parial_app:[] t
  (* returns the determinacy of the clause and if the clause has a cut in it *)
  and assume_hd b ~is_var ~ctx ~var ~loc (tm : ScopedTerm.t) tl =
    let det_hd = get_dtype ~env:ta ~ctx ~var ~loc ~is_var b in
    Format.eprintf "assume_input for term %a with det %a@." ScopedTerm.pretty tm pp_dtype det_hd;
    (det_hd, assume_input ~ctx ~var det_hd tl)
  and check_clause ?(_is_toplevel = false) ~ctx ~var ?(has_tail_cut=false) ScopedTerm.({ loc } as t) : dtype =
    let ctx = ref (BVar.clone ctx) in
    let var = Uvar.clone var in
    let rec aux ScopedTerm.{ it; loc } =
      match it with
      | Impl (R2L, ({ it = Const b } as hd), bo) -> (b, assume_hd ~loc ~ctx:!ctx ~var:var b ~is_var:false hd [], hd, Some bo)
      | Impl (R2L, ({ it = App (b, x, xs) } as hd), bo) -> (b, assume_hd ~loc ~ctx:!ctx ~var:var b ~is_var:false hd (x::xs), hd, Some bo)
      | Impl (R2L, ({ it = Var(b,xs) } as hd), bo) -> (b, assume_hd ~loc ~ctx:!ctx ~var:var b ~is_var:true hd xs, hd, Some bo)
      | Const b -> (b, assume_hd ~loc ~ctx:!ctx ~var:var b ~is_var:false t [], t, None)
      (* For clauses with quantified unification variables *)
      | App (n, { it = Lam (oname, _, body) }, []) when is_quantifier n ->
          ctx := BVar.add_oname ~new_:true ~loc oname (Compilation.type_ass_2func_mut ~loc ta) !ctx;
          aux body
      | App (b, x, xs) -> (b, assume_hd ~loc ~ctx:!ctx ~var:var b ~is_var:false t (x::xs), t, None)
      | Var _ -> raise (LoadFlexClause t)
      | _ -> anomaly ~loc @@ Format.asprintf "Found term %a in prop position" ScopedTerm.pretty_ it
    in
    try
      let pred_name, (det_hd, var), hd, body = aux t in
      Format.eprintf "Var is %a@." Uvar.pp var;
      let var, (det_body, err_atom), _has_top_level_cut =
        Option.(
          map (check ~ctx:!ctx ~var Det) body
          |> value ~default:(var, (Det, ScopedTerm.{ it = Discard; loc; ty = MutableOnce.make F.dummyname }), false))
      in
      let det_body = if has_tail_cut then Det else det_body in
      Format.eprintf "** END CHECKING THE CLAUSE @.";
      Format.eprintf "The var map is %a and det_body is %a@." Uvar.pp var pp_dtype det_body;

      let det_pred = get_tl det_hd in
      if not @@ (det_body <<= det_pred) ~loc then
        raise (RelationalBody (Some pred_name, Good_call.make ~exp:det_pred ~found:det_body err_atom));
      Format.eprintf "** Start checking outputs@.";
      infer_output ~pred_name ~ctx:!ctx ~var hd;
      det_pred
    with LoadFlexClause t ->
      if not has_tail_cut then
        warn ~loc:t.loc ~id:FlexClause (Format.asprintf "ignoring flexible clause: %a" ScopedTerm.pretty t);
      Det
  in
  try check_clause ~_is_toplevel:true ~ctx:BVar.empty ~var:Uvar.empty t |> ignore with
  | FatalDetError (pred_name, gc) | DetError (pred_name, gc) ->
      let Good_call.{ exp; found; term } = Good_call.get gc in
      error ~loc:term.loc
        (Format.asprintf "%sInvalid determinacy of output term %a.\n Expected: %a\n Found: %a"
            (undecl_disclaimer pred_name) ScopedTerm.pretty term pp_dtype exp pp_dtype found)
  | KError (pred_name, gc) ->
      let Good_call.{ exp; found; term } = Good_call.get gc in
      error ~loc:term.loc
        (Format.asprintf "%sInvalid determinacy of constructor argument %a.\n Expected: %a\n Found: %a"
            (undecl_disclaimer pred_name) ScopedTerm.pretty term pp_dtype exp pp_dtype found)
  | CastError (_,gc) -> 
    (let Good_call.{ exp; found; term } = Good_call.get gc in
        error ~loc:term.loc
          (Format.asprintf "Cast error on term %a.\n Expected: %a\n Found: %a"
              ScopedTerm.pretty term pp_dtype exp pp_dtype found))
  | RelationalBody (pred_name, gc) -> 
      let Good_call.{ term } = Good_call.get gc in
      error ~loc:term.loc 
      @@ Format.asprintf "%s@[<hov 2>Found relational atom@ @[<hov 2>(%a)@]@ in the body of function@ %a@]" (undecl_disclaimer pred_name) ScopedTerm.pretty term F.pp (let (_,n,_) = Option.get pred_name in n);

