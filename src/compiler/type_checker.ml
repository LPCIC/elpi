(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Util
open Elpi_parser
open Ast
open Compiler_data

type type_abbrevs = TypeAssignment.type_abbrevs
[@@deriving show]

type arities = Arity.t F.Map.t

let check_disjoint ~type_abbrevs ~kinds =
  kinds |> F.Map.iter (fun k (_,lock) -> if F.Map.mem k type_abbrevs then
    let { ScopedTypeExpression.loc } = F.Map.find k type_abbrevs in
    error ~loc (Format.asprintf "Type abbreviations and types must be dijoint. Type %a declared in %a" F.pp k Loc.pp lock))

open ScopedTypeExpression

let check_param_unique ~loc c ctx =
  if F.Set.mem c ctx then
    error ~loc ("Duplicate type parameter " ^ F.show c)

let check_param_exists ~loc c ctx =
  if not @@ F.Set.mem c ctx then
    error ~loc (Format.asprintf "Unknown type parameter %a. Known parameters: %a" F.pp c (pplist F.pp ", ") (F.Set.elements ctx))

let check_global_exists ~loc c (type_abbrevs : type_abbrevs) arities nargs =
  if F.Map.mem c arities then begin
    let arity, _ = F.Map.find c arities in
    if arity != nargs then
      error ~loc (Format.asprintf "Type %a expects %d arguments but was given %d" F.pp c arity nargs)
  end else if F.Map.mem c type_abbrevs then begin
    let arity = TypeAssignment.nparams @@ fst @@ F.Map.find c type_abbrevs in
    if arity != nargs then
      error ~loc (Format.asprintf "Type %a expects %d arguments but was given %d" F.pp c arity nargs)
  end else
    error ~loc ("Unknown type " ^ F.show c)

let error_unknown_target ~loc =
  error ~loc (Format.asprintf "Unknown target type. It is a predicate or not?")

(* Converts a ScopedTypeExpression into a TypeAssignment *)
let rec check_loc_tye ~positive ~type_abbrevs ~kinds ctx { loc; it } =
  check_tye ~loc ~positive ~type_abbrevs ~kinds ctx it
and check_tye ~loc ~positive ~type_abbrevs ~kinds ctx = function
  | Any when positive -> error_unknown_target ~loc
  | Any -> TypeAssignment.Any
  | Prop p -> Prop p
  | Const(Bound _,c) -> check_param_exists ~loc c ctx; UVar c
  | Const(Global _,c) -> check_global_exists ~loc c type_abbrevs kinds 0; Cons c
  | App(_,c,x,xs) ->
      check_global_exists ~loc c type_abbrevs kinds (1 + List.length xs);
      App(c,check_loc_tye ~positive ~type_abbrevs ~kinds ctx x, List.map (check_loc_tye ~positive ~type_abbrevs ~kinds ctx) xs)
  | Arrow(m,v,s,t) -> Arr(TypeAssignment.MVal m,v,check_loc_tye ~positive:false ~type_abbrevs ~kinds ctx s,check_loc_tye ~positive:true ~type_abbrevs ~kinds ctx t)


let check_type ~type_abbrevs ~kinds ~loc ~name ctx x =
  (* Format.eprintf "check_type under %a\n%!" (F.Map.pp (fun fmt (n,_) -> ())) kinds;
  Format.eprintf "check_type %a\n%!" ScopedTypeExpression.pp_v_ x;  *)
  let rec aux_params ~loc ctx = function
    | Lam(c,t) ->
        check_param_unique ~loc c ctx;
        TypeAssignment.Lam(c,aux_params ~loc (F.Set.add c ctx) t)
    | Ty t -> TypeAssignment.Ty(check_loc_tye ~positive:true ~type_abbrevs ~kinds ctx t)
  in
    aux_params ~loc ctx x

type indexing_pair = {static:Elpi_runtime.Data.indexing;runtime:Elpi_runtime.Data.indexing}
[@@deriving show]

let chose_indexing predicate l k =
  let open Elpi_runtime.Data in
  let all_zero = List.for_all ((=) 0) in
  let rec check_map default argno = function
    | [] -> error ("Wrong indexing for " ^ F.show predicate ^ ": no argument selected.")
    | 0 :: l -> check_map default (argno+1) l
    | 1 :: l when all_zero l -> MapOn argno
    | _ -> default ()
  in
  (* Format.eprintf "Index for %a is %a@." F.pp predicate (pplist pp_int ",  ") l; *)
  let pairify t = {static=DiscriminationTree l; runtime=t} in
  match k with
  | Some Ast.Structured.DiscriminationTree -> pairify @@ DiscriminationTree l
  | Some HashMap -> pairify @@ Hash l
  | None -> pairify @@ check_map (fun () -> DiscriminationTree l) 0 l
  | Some Map -> pairify @@ check_map (fun () ->
      error ("Wrong indexing for " ^ F.show predicate ^
              ": Map indexes exactly one argument at depth 1")) 0 l

let maximize_indexing_input modes =
  let open Elpi_runtime.Data in
  let depths = List.map (function Util.Mode.Fo Input | Util.Mode.Ho (Input, _) -> max_int | _ -> 0) modes in
  DiscriminationTree depths

let rec is_prop ~type_abbrevs = function
  | TypeAssignment.Lam (_,x) -> is_prop ~type_abbrevs x
  | Ty t ->  TypeAssignment.is_prop ~type_abbrevs t

let check_indexing ~loc ~type_abbrevs availability name ty indexing =
  let is_prop, mode = TypeAssignment.skema_to_func_mode ~type_abbrevs ty in
  let ensure_pred is_prop =
    if Option.is_none is_prop then
      error ~loc "Indexing directive is for predicates only" in
  let overlap indexing =
    match is_prop with
    | None | Some Relation -> Elpi_runtime.Data.Allowed
    | Some Function -> Elpi_runtime.Data.mk_Forbidden indexing in
  match indexing with
  | Some (Ast.Structured.Index(l,k)) -> ensure_pred is_prop;
      let {static;runtime} = chose_indexing name l k in
      let overlap = overlap static in
      TypingEnv.Index {mode;indexing=runtime; overlap; has_local_without_cut=None}
  | Some MaximizeForFunctional when availability = Ast.Structured.Elpi -> ensure_pred is_prop;
      let indexing = maximize_indexing_input mode in
      let overlap = overlap indexing in
      Index {mode;indexing=MapOn 0; overlap; has_local_without_cut=None}
  | _ when Option.is_some is_prop ->
      let {static;runtime} = chose_indexing name [1] None in
      let overlap = overlap static in
      TypingEnv.Index {mode;indexing=runtime; overlap; has_local_without_cut=None}
  | _ -> DontIndex

let check_type ~type_abbrevs ~kinds { value; loc; name; index; availability } : Symbol.t * Symbol.t option * TypingEnv.symbol_metadata =
  let ty = check_type ~type_abbrevs ~kinds ~loc ~name F.Set.empty value in
  (* Format.eprintf " - %a : %a\n%!" F.pp name TypeAssignment.pretty_skema ty; *)
  let indexing = check_indexing ~loc ~type_abbrevs availability name ty index in
  let symb = Symbol.make (File loc) name in
  let quotient =
    let to_unify must bsymb =
      match Symbol.RawMap.find bsymb Elpi_runtime.Data.Global_symbols.table.s2ct with
      | _ -> Some bsymb 
      | exception Not_found when must -> error ~loc ("Symbol " ^ Symbol.pretty bsymb ^ " marked as external is not declared in OCaml.\nCheck for calls to Constants.declare_global_symbol")
      | exception Not_found -> None in
    match availability with
    | Elpi -> None
    | OCaml (File _) -> anomaly "provenance File cannot be provided by the user"
    | OCaml Core -> Symbol.make Core name |> to_unify (Option.is_none (is_prop ~type_abbrevs ty))
    | OCaml (Builtin { variant } as b) -> Symbol.make b name |> to_unify (variant != 0) (* TODO: this is hack for builtins, they could be overloaded as well *)
    (* | OCaml None -> Symbol.make_builtin name |> to_unify false  *)
  in
  symb, quotient, { ty; indexing; availability }

let arrow_of_args args ety =
  let rec aux = function
  | [] -> ety
  | x :: xs -> TypeAssignment.Arr(TypeAssignment.MRef (MutableOnce.make F.dummyname),NotVariadic,ScopedTerm.type_of x,aux xs) in
  aux args

let arrow_of_tys tys ety =
  let rec aux = function
    | [] -> ety
    | (m,x) :: xs -> TypeAssignment.Arr(m,Ast.Structured.NotVariadic,x,aux xs) in
  aux tys


type runtime_types = Symbol.t F.Map.t
[@@deriving show]

let empty_runtime_types = F.Map.empty
let compile_for_runtime ({ TypingEnv.overloading } as e) =
  F.Map.filter_map (fun _ -> function TypeAssignment.Single s -> Some (TypingEnv.canon e s) | _ -> None) overloading
let runtime_resolve m f = F.Map.find f m

let check_1types k ~type_abbrevs ~kinds lst : TypingEnv.t list =
  List.map (check_type ~type_abbrevs ~kinds) lst |>
  List.map (function
  | (x,None,metadata) ->
      let overloading = F.Map.(add k (TypeAssignment.Single x) empty) in
      let symbols = Symbol.QMap.(add x metadata empty) in
      { TypingEnv.overloading; symbols }
  | (x,Some q,metadata) ->
    let overloading = F.Map.(add k (TypeAssignment.Single x) empty) in
    let symbols = Symbol.QMap.(add x metadata empty) in
    let symbols = Symbol.QMap.unify (fun _ _ _ -> anomaly "builtins predicates are unique") x q symbols in
    { TypingEnv.overloading; symbols })

let check_types ~type_abbrevs ~kinds (m : t list F.Map.t) =
  let tel = F.Map.mapi (fun k tl ->
    (* Format.eprintf "Types for %a\n%!" F.pp k; *)
    check_1types k ~type_abbrevs ~kinds tl) m in
  F.Map.fold (fun _ l acc -> List.fold_left TypingEnv.merge_envs acc l) tel TypingEnv.empty

type env_undeclared = (TypeAssignment.t * Symbol.t) F.Map.t
[@@deriving show]

open ScopedTerm

let pretty_ty valid_mode =
  if valid_mode then TypeAssignment.pretty_mut_once
  else TypeAssignment.pretty_mut_once_raw


let error ~loc msg = error ~loc ("Typechecker: " ^ msg)

let error_not_a_function ~loc c tyc args x =
  let t =
    if args = [] then ScopedTerm.App(mk_const (Scope.mkGlobal ~escape_ns:true ()) c loc,[])
    else ScopedTerm.(App(mk_const (Scope.mkGlobal ~escape_ns:true ()) c loc,args)) in
  let msg = Format.asprintf "@[<hov>%a is not a function but it is passed the argument@ @[<hov>%a@].@ The type of %a is %a@]"
    ScopedTerm.pretty_ t ScopedTerm.pretty x F.pp c TypeAssignment.pretty_mut_once tyc in
  error ~loc msg

let pp_tyctx fmt = function
  | None -> Format.fprintf fmt "its context"
  | Some c -> Format.fprintf fmt "%a" F.pp c

let error_ambiguous ~loc c alltys =
  let pretty_ty = pretty_ty true in
  let msg = Format.asprintf "@[<v>%a is overloaded. Its types are:@,@[<v 2>  %a@]@]" F.pp c (pplist (fun fmt (_,x)-> Format.fprintf fmt "%a" pretty_ty x) ", ") alltys in
  error ~loc msg

let error_bad_cdata_ety ~loc ~tyctx ~ety c tx =
  let pretty_ty = pretty_ty true in
  let msg = Format.asprintf "@[<hov>literal \"%a\" has type@ %a@ but %a expects a term of type@ %a@]"  CData.pp c pretty_ty tx pp_tyctx tyctx pretty_ty ety in
  error ~loc msg

let error_bad_ety ~valid_mode ~loc ~tyctx ~ety pp c tx =
  let pretty_ty = pretty_ty !valid_mode in
  let msg = Format.asprintf "@[<hov>%a has type@ %a@ but %a expects a term of type@ %a@]"  pp c pretty_ty tx pp_tyctx tyctx pretty_ty ety in
  error ~loc msg

let error_bad_ety2 ~valid_mode ~loc ~tyctx ~ety1 ~ety2 pp c tx =
  let pretty_ty = pretty_ty !valid_mode in
  let msg = Format.asprintf "@[<hov>%a has type@ %a@ but %a expects a term of type@ %a@ or %a@]"  pp c pretty_ty tx pp_tyctx tyctx pretty_ty ety1 pretty_ty ety2 in
  error ~loc msg

let error_bad_function_ety ~valid_mode ~loc ~tyctx ~ety c t =
  let pretty_ty = pretty_ty !valid_mode in
  let msg = Format.asprintf "@[<hov>%a is a function@ but %a expects a term of type@ %a@]"  ScopedTerm.pretty_ ScopedTerm.(Lam(c,None,t)) pp_tyctx tyctx pretty_ty ety in
  error ~loc msg

let error_bad_const_ety_l ~valid_mode ~loc ~tyctx ~ety c txl =
  let pretty_ty = pretty_ty !valid_mode in
  let msg = Format.asprintf "@[<hv>%a is overloaded but none of its types matches the type expected by %a:@,  @[<hov>%a@]@,Its types are:@,@[<v 2>  %a@]@]" F.pp c pp_tyctx tyctx pretty_ty ety (pplist ~boxed:true (fun fmt (_,x)-> Format.fprintf fmt "%a" pretty_ty x) ", ") txl in
  error ~loc msg

let error_too_many_const_ety_l ~valid_mode ~loc ~tyctx ~ety c txl =
  let pretty_ty = pretty_ty !valid_mode in
  let msg = Format.asprintf "@[<hv>%a is overloaded but too many of its types match the type expected by %a:@,  @[<hov>%a@]@,Matching types are:@,@[<v 2>  %a@]@]" F.pp c pp_tyctx tyctx pretty_ty ety (pplist ~boxed:true (fun fmt (s,x)-> Format.fprintf fmt "%a (defined at %a)" pretty_ty x Loc.pp (Symbol.get_loc s)) ", ") txl in
  error ~loc msg

let error_overloaded_app ~valid_mode ~loc ~ety c args alltys =
  let ty = arrow_of_args args ety in
  let pretty_ty = pretty_ty !valid_mode in
  let msg = Format.asprintf "@[<v>%a is overloaded but none of its types matches:@,  @[<hov>%a@]@,Its types are:@,@[<v 2>  %a@]@]" F.pp c pretty_ty ty (pplist (fun fmt (_,x)-> Format.fprintf fmt "%a" pretty_ty x) ", ") alltys in
  error ~loc msg
  
let error_overloaded_app_ambiguous ~valid_mode ~loc ~ety c args alltys =
  let ty = arrow_of_args args ety in
  let pretty_ty = pretty_ty !valid_mode in
  let msg = Format.asprintf "@[<v>%a is overloaded but too many of its types match:@,  @[<hov>%a@]@,Matching types are:@,@[<v 2>  %a@]@]" F.pp c pretty_ty ty (pplist ~boxed:true (fun fmt (s,x)-> Format.fprintf fmt "%a (defined at %a)" pretty_ty x Loc.pp (Symbol.get_loc s)) ", ") alltys in
  error ~loc msg

let error_overloaded_app_tgt ~valid_mode ~loc ~ety c alltys =
  let pretty_ty = pretty_ty !valid_mode in
  let msg = Format.asprintf "@[<v>%a is overloaded but none of its types make it build a term of type @[<hov>%a@]@,Its types are:@,@[<v 2>  %a@]@]" F.pp c pretty_ty ety (pplist (fun fmt (_,x)-> Format.fprintf fmt "%a" pretty_ty x) ", ") alltys in
  error ~loc msg


let error_not_poly ~loc c ty sk =
  let pretty_ty = pretty_ty true in
  error ~loc (Format.asprintf "@[<hv>this rule imposes on %a the type@ %a@ is less general than the declared one@ %a@]"
    F.pp c
    pretty_ty ty
    pretty_ty sk)

type ret = TypeAssignment.t MutableOnce.t TypeAssignment.t_
[@@deriving show]
type ret_id = Symbol.t * TypeAssignment.t MutableOnce.t TypeAssignment.t_
[@@deriving show]
type spilled_phantoms = ScopedTerm.t list
[@@deriving show]
type sigma = { ty : TypeAssignment.t; nocc : int; binder: Symbol.t }
[@@deriving show]
type ctx = { ret : ret; binder: Symbol.t; mode : TypeAssignment.tmode }
[@@deriving show]

let mk_uvar =
  let i = ref 0 in
  fun s -> incr i; TypeAssignment.UVar(MutableOnce.make (F.from_string (s ^ string_of_int !i)))

let local_type ctx ~loc { scope = lang; name = c } : ret_id TypeAssignment.overloaded =
  let lang = match lang with Scope.Bound c -> c | _ -> assert false in
  try
    let { binder; ret } = Scope.Map.find (c,lang) ctx in
    TypeAssignment.Single (binder, ret)
  with Not_found -> anomaly ~loc "free variable"

let fresh_skema_of_overloaded_symbol c env =
  let overloaded = F.Map.find c env.TypingEnv.overloading in
  let get_fresh x = x, (Symbol.QMap.find x env.symbols).ty |> TypeAssignment.fresh |> fst in
  TypeAssignment.map_overloaded get_fresh overloaded

let global_type (unknown_global : env_undeclared ref) env ~loc c : ret_id TypeAssignment.overloaded =
  try fresh_skema_of_overloaded_symbol c env
  with Not_found ->
    (* Printf.eprintf "FOUND OMAP %s %s\n%!" (F.show c) ; *)

    try
      let ty,id = F.Map.find c !unknown_global in
      Single (id,TypeAssignment.unval ty)
    with Not_found ->
      let ty = TypeAssignment.Val (mk_uvar (Format.asprintf "Unknown_type_of_%a_" F.pp c)) in
      let id = Symbol.make (File loc) c in
      unknown_global := F.Map.add c (ty,id) !unknown_global;
      Single (id,TypeAssignment.unval ty)

type classification =
  | Simple of { srcs : (TypeAssignment.tmode * ret) list; tgt : ret }
  | Variadic of { srcs : ret list; tgt : ret }
  | Unknown

let prop = TypeAssignment.Prop Relation
let fprop = TypeAssignment.Prop Function

let rec classify_arrow = function
  | TypeAssignment.Arr(_,Variadic,x,tgt) -> Variadic { srcs = [x]; tgt }
  | UVar m when MutableOnce.is_set m -> classify_arrow (TypeAssignment.deref m)
  | (App _ | Prop _ | Cons _ | Any | UVar _) as tgt -> Simple { srcs = []; tgt }
  | TypeAssignment.Arr(m,NotVariadic,x,xs) ->
      match classify_arrow xs with
      | Simple {srcs; tgt } -> Simple { srcs = (m,x) :: srcs; tgt }
      | Unknown -> Unknown
      | Variadic { srcs; tgt } -> Variadic { srcs = x :: srcs; tgt }

let unknown_type_assignment s = TypeAssignment.Val (mk_uvar s)

let rec extend l1 l2 =
  match l1, l2 with
  | [],_ -> assert false
  | _, [] -> []
  | [x], _:: ys -> x :: extend [x] ys
  | x::xs, _::ys -> x :: extend [x] ys

let is_spill { it } =
  match it with
  | Spill _ -> true
  | _ -> false

let rec any_arg_is_spill = function
  | [] -> false
  | x :: xs -> is_spill x || any_arg_is_spill xs

let silence_linear_warn f =
  let s = F.show f in
  let len = String.length s in
  len > 0 && (s.[0] = '_' || s.[len-1] = '_')

let checker ~type_abbrevs ~kinds ~types:env ~unknown :
  (is_rule:bool -> ScopedTerm.t -> exp:TypeAssignment.t -> env_undeclared) * 
  ((_, ScopedTerm.t) Ast.Chr.t -> env_undeclared) *
  (ScopedTerm.t * Ast.Loc.t -> env_undeclared)
=
  let valid_mode = ref true in

  (* Format.eprintf "============================ checking %a\n" ScopedTerm.pretty t; *)
  let sigma : sigma F.Map.t ref = ref F.Map.empty in
  let unknown_global = ref unknown in
  let fresh_name = let i = ref 0 in fun () -> incr i; F.from_string ("%dummy"^ string_of_int !i) in
  (* let set_fresh_id = let i = ref 0 in fun x -> incr i; x := Some !i in *)

  let global_type = global_type unknown_global in

  let get_type ~loc ctx env ({ scope; name = c } as t) =
    match scope with
    | Scope.Global _ -> global_type env ~loc c
    | Bound lang -> local_type ctx ~loc t
  in

  let rec check ~positive (ctx : ctx Scope.Map.t) ~loc ~tyctx x ety : spilled_phantoms =
    (* Format.eprintf "@[<hov 2>checking %a : %a@]\n" ScopedTerm.pretty_ x TypeAssignment.pretty_mut_once ety; *)
    match x with
    | Impl(b,_,t1,t2) -> check_impl ~positive ctx ~loc ~tyctx b t1 t2 ety
    | App({ scope = Global _} as c,[]) -> check_global ctx ~loc ~tyctx c ety
    | App({ scope = Bound _} as c,[]) -> check_local ctx ~loc ~tyctx c ety
    | CData c -> check_cdata ~loc ~tyctx kinds c ety
    | Spill(_,{contents = Phantom _}) -> assert false
    | Spill(sp,info) -> 
      if not positive then error ~loc "Spilling in negative position is forbidden";
      check_spill ~positive ctx ~loc ~tyctx sp info ety
    | App({ scope = gid } as hd,xs) -> check_app ~positive ctx ~loc ~tyctx hd (get_type ~loc ctx env hd) xs ety 
    | Lam(c,cty,t) -> check_lam ~positive ctx ~loc ~tyctx c cty t ety
    | Discard -> []
    | Var({ name = c } as hd,args) -> check_app ~positive ctx ~loc ~tyctx hd (uvar_type ~loc c) args ety
    | Cast(t,ty) ->
        let ty = TypeAssignment.subst (fun f -> Some (UVar(MutableOnce.make f))) @@ check_loc_tye ~positive:true ~type_abbrevs ~kinds F.Set.empty ty in
        let spills = check_loc ~positive ctx ~tyctx:None t ~ety:ty in
        if unify ty ety then spills
        else error_bad_ety ~valid_mode ~loc ~tyctx ScopedTerm.pretty_ x ty ~ety

  and resolve_gid ~loc id gid ety ty =
    if not @@ MutableOnce.is_set ty then MutableOnce.set ~loc ty (TypeAssignment.Val ety);
    match gid with
    | Scope.Global x -> 
      (* Format.eprintf "resolving %a\n" Symbol.pp id; *)
      SymbolResolver.resolve env x.resolved_to id
    | _ -> ()

  and check_impl ~positive ctx ~loc ~tyctx b t1 t2 ety =
    if not @@ unify ety prop then
      error_bad_ety ~valid_mode ~loc ~tyctx ~ety:prop ScopedTerm.pretty_ (Impl(b,loc,t1,t2)) (ety)
    else
      let lhs, rhs,c,positive (* of => *) =
        match b with
        | L2R -> t1,t2,F.implf,positive
        | L2RBang -> t1,t2,F.implbangf,positive
        | R2L -> t2,t1,F.rimplf,not positive in
      let spills = check_loc ~positive ~tyctx:(Some c) ctx rhs ~ety:prop in
      let lhs_ty = mk_uvar "Src" in
      let more_spills = check_loc ~positive:(not positive) ~tyctx:None ctx ~ety:lhs_ty lhs in
      let ety1 = prop in
      let ety2 = TypeAssignment.App(F.from_string "list",prop,[]) in
      if try_unify lhs_ty ety1 then spills @ more_spills (* probably an error if not empty *)
      else if unify lhs_ty (ety2) then spills @ more_spills (* probably an error if not empty *)
      else error_bad_ety2 ~valid_mode ~tyctx:(Some c) ~loc ~ety1 ~ety2  ScopedTerm.pretty lhs lhs_ty

  and check_global ctx ~loc ~tyctx { scope = gid; name = c; ty = tya } ety =
    match global_type env ~loc c with
    | Single (id,ty) ->
        if unify ty ety then (resolve_gid ~loc id gid ty tya; [])
        else error_bad_ety ~valid_mode ~tyctx ~loc ~ety F.pp c ty
    | Overloaded l ->
        only_one_unifies ~loc ~valid_mode ~tyctx gid c tya l ety; []

  and check_local ctx ~loc ~tyctx ({ name = c; ty = tya} as t) ety =
    match local_type ctx ~loc t with
    | Single (id,ty) ->
        if unify ty ety then (
          if not @@ MutableOnce.is_set tya then MutableOnce.set tya (Val ty); [])
        else error_bad_ety ~valid_mode ~tyctx ~loc ~ety F.pp c ty
    | Overloaded _ -> assert false

  and check_cdata ~loc ~tyctx kinds c ety =
    let name = F.from_string @@ CData.name c in
    check_global_exists ~loc name type_abbrevs kinds 0;
    let ty = TypeAssignment.Cons name in
    if unify ty ety then []
    else error_bad_cdata_ety ~tyctx ~loc c ty ~ety

  and check_lam ~positive ctx ~loc ~tyctx sc c_type_cast t ety =
    let { scope = name_lang; name = c; ty = c_type } = match sc with Some c -> c | None -> mk_const elpi_language (fresh_name ()) loc in
    let src = match c_type_cast with
      | None -> mk_uvar "Src"
      | Some x -> TypeAssignment.subst (fun f -> Some (UVar(MutableOnce.make f))) @@ check_loc_tye ~positive:true ~type_abbrevs ~kinds F.Set.empty x
    in
    if not @@ MutableOnce.is_set c_type then MutableOnce.set ~loc c_type (Val src);
    (* Format.eprintf "Ty is setted to %a@." (MutableOnce.pp TypeAssignment.pp) (tya); *)
    let tgt = mk_uvar "Tgt" in
    (* let () = Format.eprintf "lam ety %a\n" TypeAssignment.pretty ety in *)
    let mode = TypeAssignment.MRef (MutableOnce.make F.dummyname) in
    if unify (TypeAssignment.Arr(mode, Ast.Structured.NotVariadic,src,tgt)) ety then
      (* let () = Format.eprintf "add to ctx %a : %a\n" F.pp name TypeAssignment.pretty src in *)
      let ctx = Scope.Map.add (c,name_lang) { ret = src; mode; binder = Symbol.make (File loc) c } ctx in
      check_loc ~positive ~tyctx ctx t ~ety:tgt
    else
      error_bad_function_ety ~valid_mode ~loc ~tyctx ~ety sc t

  and check_spill ~positive(*TODO*) ctx ~loc ~tyctx sp info ety =
    let inner_spills = check_spill_conclusion_loc ~positive ~tyctx:None ctx sp ~ety:(TypeAssignment.(Arr(MRef (MutableOnce.make F.dummyname), Ast.Structured.NotVariadic,ety,mk_uvar "Spill"))) in
    assert(inner_spills = []);
    let phantom_of_spill_ty i ty =
      { loc; it = Spill(sp,ref (Phantom(i+1))); ty = TypeAssignment.create ty } in
    match classify_arrow (ScopedTerm.type_of sp) with
    | Simple { srcs; tgt } ->
        if not @@ unify tgt prop then error ~loc "only predicates can be spilled";
        let spills = List.map snd srcs in
        if spills = [] then
          error ~loc "nothing to spill, the expression lacks no arguments";
        let (first_spill) = List.hd spills in
        if unify first_spill ety then begin
          info := Main (List.length spills);
          List.mapi phantom_of_spill_ty @@ List.tl spills
        end
        else error_bad_ety ~valid_mode ~tyctx ~loc ~ety ScopedTerm.pretty_ (Spill(sp,info)) first_spill
    | _ -> error ~loc "hard spill"

  and unify_tgt_ety n ety (_,t) = 
    match classify_arrow t with
    | Unknown -> true
    | Simple { srcs; tgt } ->
        let nsrcs = List.length srcs in
        if n > nsrcs then false
        else
          let rec drop i l = if i = 0 then l else drop (i-1) (List.tl l) in
          let srcs = drop n srcs in unify_then_undo (arrow_of_tys srcs tgt) ety
    | Variadic _ -> true (* TODO *)

  and check_app ~positive ctx ~loc ~tyctx { scope = cid; name = c; ty = tya; loc = cloc } cty args ety =
    match cty with
    | Overloaded all ->
      (* Format.eprintf "@[options %a %a %d:@ %a@]\n" F.pp c TypeAssignment.pretty_mut_once ety (List.length args) (pplist (fun fmt (_,x) -> TypeAssignment.pretty_mut_once fmt x) "; ") l; *)
      let l = List.filter (unify_tgt_ety (List.length args) ety) all in
      begin match l with
      | [] -> error_overloaded_app_tgt ~valid_mode ~loc ~ety c all
      | [ty] -> 
      (* Format.eprintf "1option left: %a\n" TypeAssignment.pretty (snd ty); *)
        check_app ~positive ctx ~loc ~tyctx { scope = cid; name = c; ty = tya; loc = cloc } (Single ty) args ety
      | l ->
      (* Format.eprintf "newoptions: %a\n" (pplist (fun fmt (_,x) -> TypeAssignment.pretty fmt x) "; ") l; *)
          let args = List.concat_map (fun x -> x :: check_loc ~positive ~tyctx:None ctx ~ety:(mk_uvar (Format.asprintf "Ety_%a" F.pp c)) x) args in
          let targs = List.map ScopedTerm.type_of args in
          check_app_overloaded ~positive ctx ~loc (c,cid,tya) ety args targs l l
      end
    | Single (id,ty) ->
      (* Format.eprintf "%a: 1 option: %a@." F.pp c TypeAssignment.pretty_mut_once_raw ty; *)
        let err ty =
          if args = [] then error_bad_ety ~valid_mode ~loc ~tyctx ~ety F.pp c ty (* uvar *)
          else error_bad_ety ~valid_mode ~loc ~tyctx ~ety ScopedTerm.pretty_ (App(mk_const (Scope.mkGlobal ~escape_ns:true ()(* sucks *)) c loc,args)) ty in
        let monodirectional () =
          (* Format.eprintf "checking app mono %a\n" F.pp c; *)
          let tgt = check_app_single ~positive ctx ~loc (cid,c,tya) ty [] args in
          if unify tgt ety then (resolve_gid ~loc id cid ty tya; [])
          else err tgt in
        let bidirectional srcs tgt =
          (* Format.eprintf "checking app bidi %a\n" F.pp c; *)
          let rec consume args srcs =
            match args, srcs with
            | [], srcs -> arrow_of_tys srcs tgt
            | _ :: args, _ :: srcs -> consume args srcs
            | _ :: _, [] -> assert false
          in
          let rest_tgt = consume args srcs in
          (* Format.eprintf "Setting the type of %a to %a old is %a (%a)@." F.pp c TypeAssignment.pretty_mut_once ty (TypeAssignment.pretty_mut_once) (UVar tya) Loc.pp loc; *)
          if unify rest_tgt ety then
            let _ = check_app_single ~positive ctx ~loc (cid,c,tya) ty [] args in (resolve_gid ~loc id cid ty tya; [])
          else err rest_tgt in
        match classify_arrow ty with
        | Unknown | Variadic _ -> monodirectional ()
        | Simple { srcs; tgt } ->
          if List.length args > List.length srcs then monodirectional () (* will error *)
          else
            if any_arg_is_spill args then monodirectional ()
            else bidirectional srcs tgt

  (* REDO PROCESSING ONE SRC at a time *)
  and check_app_overloaded ~positive ctx ~loc (c, cid, tya) ety args targs alltys l =
    let rec filter = function
    | [] -> []
    | (id,t)::ts ->
        (* Format.eprintf "checking overloaded app %a\n" F.pp c; *)
        let decore_with_dummy_mode =  List.map (fun x -> (TypeAssignment.MRef (MutableOnce.make F.dummyname),x)) in
        match classify_arrow t with
        | Unknown -> error ~loc (Format.asprintf "Type too ambiguous to be assigned to the overloaded constant: %s for type %a" (F.show c) (pretty_ty true) t)
        | Simple { srcs; tgt } ->
          (* Format.eprintf "argsty : %a\n" TypeAssignment.pretty (arrow_of_tys targs ety); *)
            let ul = (arrow_of_tys srcs tgt) in 
            let ur = (arrow_of_tys (decore_with_dummy_mode targs) ety) in 
            if unify_then_undo ul ur then  ((id,t),(ul,ur))::filter ts else filter ts
        | Variadic { srcs ; tgt } ->
            let srcs = extend srcs targs |> decore_with_dummy_mode in
            let ul = (arrow_of_tys srcs tgt) in 
            let ur = (arrow_of_tys (decore_with_dummy_mode targs) ety) in 
            if unify_then_undo ul ur then ((id,t),(ul,ur))::filter ts else filter ts
  in
  match filter l with
  | [] -> error_overloaded_app ~valid_mode ~loc c args ~ety alltys
  | [(id,t),(ul,ur)] -> 
      assert(unify ul ur);
      resolve_gid ~loc id cid t tya;[]
  | l -> error_overloaded_app_ambiguous ~valid_mode ~loc c args ~ety (List.map fst l)

  and infer_mode ctx m { loc; it } =
    match it with
    | App({ scope = Scope.Bound l; name = f; ty },[]) ->
        begin match Scope.Map.find_opt (f,l) ctx with
        | None ->  anomaly "unbound"
        | Some info ->
            if TypeAssignment.is_tmode_set info.mode || fst @@ unif_mode false ~positive:true info.mode m then ()
            else error ~loc ("mode mismatch on bound variable " ^ F.show f)
      end
    | _ -> ()

  and check_app_single ~positive ctx ~loc (_,c,_ as fc) ty consumed args =
    match args with
    | [] -> ty
    | x :: xs ->
      (* Format.eprintf "@[<h>Checking term %a with type %a@]@." ScopedTerm.pretty x TypeAssignment.pretty_mut_once_raw ty;
      Format.eprintf "checking app %a against %a@." ScopedTerm.pretty_ (ScopedTerm.App(fc,x,xs)) TypeAssignment.pretty_mut_once_raw ty; *)
      match ty with
        | TypeAssignment.Arr(_, Variadic,s,t) ->
            let xs = check_loc_if_not_phantom ~positive ~tyctx:(Some c) ctx x ~ety:s @ xs in
            if xs = [] then t else check_app_single ~positive ctx ~loc fc ty (x::consumed) xs
        | Arr(m,NotVariadic,s,t) ->
            let xs = check_loc_if_not_phantom ~positive ~tyctx:(Some c) ctx x ~ety:s @ xs in
            (* Format.eprintf "-- Checked term %a with ety %a; mode is %a@." ScopedTerm.pretty x TypeAssignment.pretty_mut_once s TypeAssignment.pretty_tmode m; *)
            infer_mode ctx m x;
          check_app_single ~positive ctx ~loc fc t (x::consumed) xs
        | Any -> check_app_single ~positive ctx ~loc fc ty (x::consumed) xs
        | UVar m when MutableOnce.is_set m ->
            check_app_single ~positive ctx ~loc fc (TypeAssignment.deref m) consumed (x :: xs)
        | UVar m ->
            let s = mk_uvar "Src" in
            let t = mk_uvar "Tgt" in
            let _ = unify ty (TypeAssignment.Arr(MRef (MutableOnce.make F.dummyname),Ast.Structured.NotVariadic,s,t)) in
            check_app_single ~positive ctx ~loc fc ty consumed (x :: xs)
        | Cons a when F.Map.mem a type_abbrevs ->
            let ty = TypeAssignment.apply (fst @@ F.Map.find a type_abbrevs) [] in
            check_app_single ~positive ctx ~loc fc ty consumed args
        | App(a,x,xs) when F.Map.mem a type_abbrevs ->
            let ty = TypeAssignment.apply (fst @@ F.Map.find a type_abbrevs) (x::xs) in
            check_app_single ~positive ctx ~loc fc ty consumed args
        | _ -> error_not_a_function ~loc:x.loc c ty (List.rev consumed) x (* TODO: trim loc up to x *)

  and check_loc ~positive ~tyctx ctx { loc; it; ty } ~ety : spilled_phantoms =
      begin
        let extra_spill = check ~positive ~tyctx ctx ~loc it ety in
        if not @@ MutableOnce.is_set ty then MutableOnce.set ty (Val ety);
        extra_spill
      end

  and check_loc_if_not_phantom ~positive ~tyctx ctx x ~ety : spilled_phantoms =
    match x.it with
    | Spill(_,{ contents = Phantom _}) -> []
    | _ -> check_loc ~positive ~tyctx ctx x ~ety

  and check_spill_conclusion_loc ~positive ~tyctx ctx { loc; it; ty } ~ety : spilled_phantoms =
    (* A spill can be duplicate by a macro for example *)
    let already_typed = MutableOnce.is_set ty in
    let extra_spill = check_spill_conclusion ~positive ~tyctx ctx ~loc it ety in
    if not already_typed then MutableOnce.set ty (Val ety);
    extra_spill

  (* This descent to find the spilled term is a bit ad hoc, since it
  inlines => and , typing... but leaves the rest of the code clean *)
  and check_spill_conclusion ~positive ~tyctx ctx ~loc it ety =
    match it with
    | Impl((L2R|L2RBang),_,x,y) ->
        let lhs = mk_uvar "LHS" in
        let spills = check_loc ~positive ~tyctx ctx x ~ety:lhs in
        if spills <> [] then error ~loc "Hard spill";
        if try_unify lhs prop || try_unify lhs (App(F.from_string "list",prop,[]))
        then check_spill_conclusion_loc ~positive ~tyctx ctx y ~ety
        else error ~loc "Bad impl in spill"
    | App({ scope = Global _; name = c; ty = tya } as sc,x::xs) when F.equal c F.andf ->
        let _ = check_global ctx ~loc ~tyctx sc (mk_uvar "spill_and") in
        let spills = check_loc ~positive ~tyctx ctx x ~ety:fprop in
        if spills <> [] then error ~loc "Hard spill";
        begin match xs with
        | [] -> assert false
        | [x] -> check_loc ~positive ~tyctx ctx x ~ety
        | x::xs -> check_spill_conclusion ~positive ~tyctx ctx ~loc (App(sc,x::xs)) ety
        end
    | _ -> check ~positive ~tyctx ctx ~loc it ety

  and check_matches_poly_skema_loc ~unknown { loc; it } =
    let c, args =
      let rec head it =
        match it with
        | App({ scope = Global _; name = f },[{ it = Lam(_,_,x) }]) when F.equal F.pif f -> head x.it
        | Impl(R2L,_,{ it = App({ scope = Global _; name = c' },xs) },_) -> c', xs
        | App({ scope = Global _; name = c },xs) -> c, xs
        | _ -> anomaly ~loc ("not a rule: " ^ ScopedTerm.show_t_ it) in
      head it in
    (* Format.eprintf "Checking %a\n" F.pp c; *)
    match F.Map.find c env.overloading with
    | Single id ->
      begin match (Symbol.QMap.find id env.symbols).ty with
      | Ty _ -> ()
      | Lam _ as sk -> check_matches_poly_skema ~loc ~pat:(TypeAssignment.fresh sk) c (arrow_of_args args prop)
      end
    | Overloaded _ -> ()
    | exception Not_found -> assert(F.Map.mem c unknown)

  and check_matches_poly_skema ~loc ~pat c ty =
    if try_matching ~pat ty then () else error_not_poly ~loc c ty (fst pat)

  and try_unify x y =
    let vx = TypeAssignment.vars_of (Val x) in
    let vy = TypeAssignment.vars_of (Val y) in
    let b = unify x y in
    if not b then (undo vx; undo vy);
    b

  and unify_then_undo x y =
    let vx = TypeAssignment.vars_of (Val x) in
    let vy = TypeAssignment.vars_of (Val y) in
    let b = unify x y in
    undo vx; undo vy;
    b
    
  and only_one_unifies ~loc ~valid_mode ~tyctx gid c tya l ety =
    let vars = TypeAssignment.vars_of (Val ety) in
    let rec filter_unif = function
      | [] -> []
      | (id, x) :: xs ->
        if unify x ety then (undo vars; (id,x) :: filter_unif xs) else (undo vars; filter_unif xs) in
    match filter_unif l with
    | [] -> error_bad_const_ety_l ~valid_mode ~tyctx ~loc ~ety c l
    | [id, x] -> assert(unify x ety); resolve_gid ~loc id gid x tya
    | l -> error_too_many_const_ety_l ~valid_mode ~tyctx ~loc ~ety c l
  
  and undo ((l_ty : TypeAssignment.t MutableOnce.t list), (l_m : TypeAssignment.tmode MutableOnce.t list)) =
    List.iter MutableOnce.unset l_ty;
    List.iter MutableOnce.unset l_m

  and unif_mode ~positive matching m1 m2 =
    let (<=) (m1 : Mode.t) (m2 : Mode.t) =
      match m1, m2 with
      | Input, Input -> true, not positive
      | Output, Input -> positive, not positive
      | Output, Output -> true, positive
      | Input, Output -> not positive, positive
    in
    let m1, m2 = TypeAssignment.(deref_tmode m1, deref_tmode m2) in
    match m1, m2 with
    | MVal m1, MVal m2 -> m1 <= m2
    | MRef _, MVal _ when matching -> false, not positive
    | MRef m1, MRef m2 when m1 == m2 -> true, not positive
    | MRef m1, _ -> MutableOnce.set m1 m2; true, not positive
    | _, MRef m2 -> MutableOnce.set m2 m1; true, not positive

  and uvar_type ~loc c =
    try
      let { ty; nocc; binder } as info = F.Map.find c !sigma in
      sigma := F.Map.add c { info with nocc = nocc+1 } !sigma;
      Single (binder, TypeAssignment.unval @@ ty)
    with Not_found ->
      let ty = TypeAssignment.UVar (MutableOnce.make c) in
      let binder = Symbol.make (File loc) c in
      sigma := F.Map.add c { ty = TypeAssignment.Val ty; nocc = 1; binder } !sigma;
      Single (binder, ty)
  (* matching=true -> X = t fails (X = Y works)*)
  and unif ~matching ~positive t1 t2 =
    (* Format.eprintf "%a = %a\n" TypeAssignment.pretty_mut_once_raw t1 TypeAssignment.pretty_mut_once_raw t2; *)
    let open TypeAssignment in
    match t1, t2 with
    | Any, _ -> true
    | _, Any -> true
    | UVar m, _ when MutableOnce.is_set m -> unif ~matching ~positive (TypeAssignment.deref m) t2
    | _, UVar m when MutableOnce.is_set m -> unif ~matching ~positive t1 (TypeAssignment.deref m)
    | App(c1,x,xs), App(c2,y,ys) when F.equal c1 c2 ->
        unif ~matching ~positive x y && Util.for_all2 (unif ~matching ~positive) xs ys
    | Cons c1, Cons c2 when F.equal c1 c2 -> true
    | Prop _, Prop _ -> true (* unification of prop is correct for tc indipendently of their functionality *)
    | App(c,Prop _,[]), Prop _ when F.equal c F.(from_string "list") -> true
    | Prop _, App(c,Prop _,[]) when F.equal c F.(from_string "list") -> true
    | Arr(m1,b1,s1,t1), Arr(m2,b2,s2,t2) -> 
      let valid, negative = unif_mode ~positive matching m1 m2 in
      valid_mode := valid;
      !valid_mode && b1 == b2 && unif ~matching ~positive:negative s1 s2 && unif ~matching ~positive t1 t2
    | Arr(_,Variadic,_,t), _ -> unif ~matching ~positive t t2 (* TODO *)
    | _, Arr(_,Variadic,_,t) -> unif ~matching ~positive t1 t (* TODO *)
    | UVar m, UVar n when matching -> assign m t2 (* see disjoint *)
    | UVar m, _ when not matching -> assign m t2
    | _, UVar m -> assign m t1
    | Cons c, _ when F.Map.mem c type_abbrevs ->
        let t1 = apply (fst @@ F.Map.find c type_abbrevs) [] in
        unif ~matching ~positive t1 t2
    | _, Cons c when F.Map.mem c type_abbrevs ->
        let t2 = apply (fst @@ F.Map.find c type_abbrevs) [] in
        unif ~matching ~positive t1 t2
    | App(c,x,xs), _ when F.Map.mem c type_abbrevs ->
        let t1 = apply (fst @@ F.Map.find c type_abbrevs) (x::xs) in
        unif ~matching ~positive t1 t2
    | _, App(c,x,xs) when F.Map.mem c type_abbrevs ->
        let t2 = apply (fst @@ F.Map.find c type_abbrevs) (x::xs) in
        unif ~matching ~positive t1 t2
    | _,_ -> false

  and unify (x: TypeAssignment.t MutableOnce.t TypeAssignment.t_) (y: TypeAssignment.t MutableOnce.t TypeAssignment.t_) =
    unif ~matching:false ~positive:true x y
  and try_matching ~pat:(x,vars) y =
    let vars = F.Map.bindings vars |> List.map snd |> List.map cell_of, [] in
    let deref x = cell_of (TypeAssignment.deref x) in
    if unif ~matching:true ~positive:true x y then
      if disjoint (List.map deref (fst vars)) then true
      else (undo vars; false)
    else
      (undo vars; false)

  and cell_of = function
    | TypeAssignment.UVar x -> x
    | _ -> assert false

  (* T1 = A -> B and T2 = C -> C do unify, but force a non injective mapping in the substitution for T1, namely { A := C , B := C } *)
  and disjoint = function
      | [] -> true
      | x :: xs -> not (List.exists (fun y -> same_var y (TypeAssignment.UVar x)) xs) && disjoint xs

  and assign m t = same_var m t || (oc m t && ((*Format.eprintf "%a := %a\n" MutableOnce.(pp TypeAssignment.pp) m TypeAssignment.(pp_t_ MutableOnce.(pp TypeAssignment.pp)) t;*)TypeAssignment.set m t; true))

  and same_var m = function
    | UVar n when n == m -> true
    | UVar n when MutableOnce.is_set n -> same_var m (TypeAssignment.deref n)
    | _ -> false

  and oc m = function
    | Prop _ -> true
    | Arr(_,_,x,y) -> oc m x && oc m y
    | App(_,x,xs) -> List.for_all (oc m) (x::xs)
    | Any -> true
    | Cons _ -> true
    | UVar n when m == n -> false
    | UVar n when MutableOnce.is_set n -> oc m (TypeAssignment.deref n)
    | UVar _ -> true

  in
    (* this is wrong, since the same unit may be checked against different contexts *)
    (* if MutableOnce.is_set t.ty then !unknown_global else *)

  let check ~is_rule t ~exp =
    let spills = check_loc ~positive:true ~tyctx:None Scope.Map.empty t ~ety:(TypeAssignment.unval exp) in
    if is_rule then check_matches_poly_skema_loc ~unknown:!unknown_global t;
    if spills <> [] then error ~loc:t.loc "cannot spill in head";
    F.Map.iter (fun k { nocc = n; binder } ->
      if n = 1 && not @@ silence_linear_warn k && is_rule then
        warn ~loc:(Symbol.get_loc binder) ~id:LinearVariable
          (Format.asprintf "%a is linear: name it _%a (discard) or %a_ (fresh variable)"
        F.pp k F.pp k F.pp k))
      !sigma;
    !unknown_global in
  let check_chr { Ast.Chr.to_match; to_remove; guard; new_goal; loc; attributes } =
    let check_sequent { Ast.Chr.context; conclusion; eigen } =
      let spills = check_loc ~positive:true ~tyctx:None Scope.Map.empty ~ety:(mk_uvar "eigen") eigen in
      if spills <> [] then error ~loc "cannot spill in eigen";
      let spills = check_loc ~positive:true ~tyctx:None Scope.Map.empty ~ety:(Prop Relation) conclusion in
      if spills <> [] then error ~loc "cannot spill in conclusion";
      let spills = check_loc ~positive:true ~tyctx:None Scope.Map.empty ~ety:(App(F.from_string "list",Prop Relation,[])) context in
      if spills <> [] then error ~loc "cannot spill in context" in
    let check_guard t =
      let spills = check_loc ~positive:true ~tyctx:None Scope.Map.empty ~ety:(Prop Relation) t in
      if spills <> [] then error ~loc "cannot spill in guard" in
    List.iter check_sequent to_match;
    List.iter check_sequent to_remove;
    Option.iter check_guard guard;
    Option.iter check_sequent new_goal;
    !unknown_global in

  let check_macro (t,loc) =
    let spills = check_loc ~positive:true ~tyctx:None Scope.Map.empty t ~ety:(mk_uvar "macro") in
    if spills <> [] then error ~loc:t.loc "cannot spill in head";
    !unknown_global in
  check, check_chr, check_macro

let check ~type_abbrevs ~kinds ~types:env ~unknown ~is_rule t ~exp =
  let check, _, _ = checker  ~type_abbrevs ~kinds ~types:env ~unknown in
  check ~is_rule t ~exp

let check_chr_rule ~type_abbrevs ~kinds ~types:env ~unknown r =
  let _, check_chr, _ = checker  ~type_abbrevs ~kinds ~types:env ~unknown in
  check_chr r

let check_macro ~type_abbrevs ~kinds ~types:env k m =
  let unknown = F.Map.empty in
  let _, _, check_macro = checker  ~type_abbrevs ~kinds ~types:env ~unknown in
  let unknown = check_macro m in
  if F.Map.is_empty unknown then ()
  else
    F.Map.iter (fun _ (_,s) -> error ~loc:(Symbol.get_loc s) ("Undeclared symbol in macro " ^ F.show k ^": " ^ Symbol.get_str s)) unknown


let check1_undeclared ~type_abbrevs w f (t, id) =
  match TypeAssignment.is_monomorphic t with
  | None -> error ~loc:(Symbol.get_loc id) Format.(asprintf "@[Unable to infer a closed type for %a:@ %a@]" F.pp f (pretty_ty true) (TypeAssignment.unval t))
  | Some (Ty tya as ty) ->
      if not @@ Re.Str.(string_match (regexp "^\\(.*aux[0-9']*\\|main\\)$") (F.show f) 0) then
        w := Format.((f, Symbol.get_loc id), asprintf "type %a %a." F.pp f (pretty_ty true) (TypeAssignment.unval t)) :: !w;
      let rec ty2mode : _ -> Util.Mode.hos = function
        | TypeAssignment.Arr (_,_,(Arr _ as l),r) -> Ast.Mode.(Ho (Output, ty2mode l)) :: ty2mode r
        | TypeAssignment.Arr (_,_,_,r) -> Ast.Mode.(Fo Output) :: ty2mode r
        | _ -> [] in
      let mode = ty2mode tya in
      let indexing = match is_prop ~type_abbrevs ty with
      | None -> TypingEnv.DontIndex
      | Some Relation -> Index {mode; indexing=MapOn 0; overlap = Allowed; has_local_without_cut=None} 
      | Some Function ->
        let {static;runtime} = chose_indexing (Symbol.get_func id) [1] None in
        TypingEnv.Index {mode;indexing=runtime; overlap=Elpi_runtime.Data.mk_Forbidden static; has_local_without_cut=None}
      in
      id, TypingEnv.{ ty ; indexing; availability = Elpi }
  | _ -> assert false

let check_undeclared ~type_abbrevs ~unknown =
  let w = ref [] in
  let unknown = F.Map.mapi (check1_undeclared ~type_abbrevs w) unknown in
  if !w <> [] then begin
    let undeclared, types = List.split !w in
    warn ~id:UndeclaredGlobal Format.(asprintf "@[<v>Undeclared globals:@ @[<v>%a@].@ Please add the following text to your program:@\n%a@]" (pplist (fun fmt (f,loc) -> Format.fprintf fmt "- %a %a" Loc.pp loc F.pp f) ", ") undeclared
     (pplist pp_print_string "") types);
  end;
  let overloading = F.Map.map (fun (x,_) -> TypeAssignment.Single x) unknown in
  let symbols = F.Map.fold (fun _ (k,v) m -> Symbol.QMap.add k v m) unknown Symbol.QMap.empty in
  { TypingEnv.overloading; symbols }

let check_pred_name ~types ~loc f =
  let undef = ref F.Map.empty in
  match global_type undef types ~loc f with
  | Single s ->
      if F.Map.is_empty !undef then fst s
      else error ~loc ("Undeclared predicate " ^ F.show f)
  | Overloaded alltys -> error_ambiguous ~loc f alltys

(* let check ~type_abbrevs a b c =
  try check ~type_abbrevs a b c with
  | CompileError(_,"Unknown global: %spill") -> Printf.eprintf "SPILLING"; exit 1
  | CompileError(_,s) when Re.Str.(string_match (regexp "Unknown global: @")) s 0 -> Printf.eprintf "MACRO"; exit 1
  | CompileError(loc,msg) -> Format.eprintf "Ignoring type error: %a %s\n" (Util.pp_option Loc.pp) loc msg; TypeAssignment.(Val Prop) *)
