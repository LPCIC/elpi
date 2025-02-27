(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Util
open Elpi_parser
open Ast
open Compiler_data

type type_abbrevs = (TypeAssignment.skema_w_id * Loc.t) F.Map.t
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

(* Converts a ScopedTypeExpression into a TypeAssignment *)
let rec check_loc_tye ~type_abbrevs ~kinds ctx { loc; it } =
  check_tye ~loc ~type_abbrevs ~kinds ctx it
and check_tye ~loc ~type_abbrevs ~kinds ctx = function
  | Any -> TypeAssignment.Any
  | Prop p -> Prop p
  | Const(Bound _,c) -> check_param_exists ~loc c ctx; UVar c
  | Const(Global _,c) -> check_global_exists ~loc c type_abbrevs kinds 0; Cons c
  | App(_,c,x,xs) ->
      check_global_exists ~loc c type_abbrevs kinds (1 + List.length xs);
      App(c,check_loc_tye ~type_abbrevs ~kinds ctx x, List.map (check_loc_tye ~type_abbrevs ~kinds ctx) xs)
  | Arrow(m,v,s,t) -> Arr(TypeAssignment.MVal m,v,check_loc_tye ~type_abbrevs ~kinds ctx s,check_loc_tye ~type_abbrevs ~kinds ctx t)


let check_type ~type_abbrevs ~kinds ~loc ctx x : TypeAssignment.skema_w_id =
  (* Format.eprintf "check_type under %a\n%!" (F.Map.pp (fun fmt (n,_) -> ())) kinds;
  Format.eprintf "check_type %a\n%!" ScopedTypeExpression.pp_v_ x;  *)
  let rec aux_params ~loc ctx = function
    | Lam(c,t) ->
        check_param_unique ~loc c ctx;
        TypeAssignment.Lam(c,aux_params ~loc (F.Set.add c ctx) t)
    | Ty t -> TypeAssignment.Ty(check_loc_tye ~type_abbrevs ~kinds ctx t)
  in
    Scope.fresh_type_decl_id loc, aux_params ~loc ctx x

let check_types  ~type_abbrevs ~kinds lst : TypeAssignment.overloaded_skema_with_id =
  match List.map (fun { value; loc } -> check_type ~type_abbrevs ~kinds ~loc F.Set.empty value) lst with
  | [] -> assert false
  | [x] -> TypeAssignment.Single x
  | xs -> TypeAssignment.Overloaded xs

let check_type  ~type_abbrevs ~kinds { value; loc } : (TypeAssignment.skema_w_id) =
  check_type ~type_abbrevs ~kinds ~loc F.Set.empty value

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

type env = TypeAssignment.overloaded_skema_with_id F.Map.t
type env_undeclared = (TypeAssignment.t * Scope.type_decl_id * Ast.Loc.t) F.Map.t
[@@deriving show]

open ScopedTerm

let pretty_ty = TypeAssignment.pretty_mut_once

let error_not_a_function ~loc c tyc args x =
  let t =
    if args = [] then ScopedTerm.Const(mk_ty_name (Scope.mkGlobal ~escape_ns:true ()) c)
    else ScopedTerm.(App(mk_ty_name (Scope.mkGlobal ~escape_ns:true ()) c,List.hd args, List.tl args)) in
  let msg = Format.asprintf "@[<hov>%a is not a function but it is passed the argument@ @[<hov>%a@].@ The type of %a is %a@]"
    ScopedTerm.pretty_ t ScopedTerm.pretty x F.pp c TypeAssignment.pretty_mut_once tyc in
  error ~loc msg

let pp_tyctx fmt = function
  | None -> Format.fprintf fmt "its context"
  | Some c -> Format.fprintf fmt "%a" F.pp c

let prettier valid_mode = if !valid_mode then pretty_ty else TypeAssignment.pretty_mut_once_raw
let error_msg_mode ~loc valid_mode msg = 
  error ~loc @@ if valid_mode then msg else "Mode error: " ^ msg

let error_bad_cdata_ety ~loc ~tyctx ~ety c tx =
  let msg = Format.asprintf "@[<hov>literal \"%a\" has type %a@ but %a expects a term of type@ %a@]"  CData.pp c pretty_ty tx pp_tyctx tyctx pretty_ty ety in
  error ~loc msg

let error_bad_ety ~valid_mode ~loc ~tyctx ~ety pp c tx =
  let msg = Format.asprintf "@[<hov>%a has type %a@ but %a expects a term of type@ %a@]"  pp c (prettier valid_mode) tx pp_tyctx tyctx (prettier valid_mode) ety in
  error_msg_mode ~loc !valid_mode msg

let error_bad_ety2 ~valid_mode ~loc ~tyctx ~ety1 ~ety2 pp c tx =
  let msg = Format.asprintf "@[<hov>%a has type %a@ but %a expects a term of type@ %a@ or %a@]"  pp c (prettier valid_mode) tx pp_tyctx tyctx (prettier valid_mode) ety1 (prettier valid_mode) ety2 in
  error_msg_mode ~loc !valid_mode msg

let error_bad_function_ety ~valid_mode ~loc ~tyctx ~ety c t =
  let msg = Format.asprintf "@[<hov>%a is a function@ but %a expects a term of type@ %a@]"  ScopedTerm.pretty_ ScopedTerm.(Lam(c,None,t)) pp_tyctx tyctx (prettier valid_mode) ety in
  error_msg_mode ~loc !valid_mode msg

let error_bad_const_ety_l ~valid_mode ~loc ~tyctx ~ety c txl =
  let msg = Format.asprintf "@[<hv>%a is overloaded but none of its types matches the type expected by %a:@,  @[<hov>%a@]@,Its types are:@,@[<v 2>  %a@]@]" F.pp c pp_tyctx tyctx (prettier valid_mode) ety (pplist ~boxed:true (fun fmt (_,x)-> Format.fprintf fmt "%a" (prettier valid_mode) x) ", ") txl in
  error_msg_mode ~loc !valid_mode msg

let error_overloaded_app ~valid_mode ~loc ~ety c args alltys =
  let ty = arrow_of_args args ety in
  let msg = Format.asprintf "@[<v>%a is overloaded but none of its types matches:@,  @[<hov>%a@]@,Its types are:@,@[<v 2>  %a@]@]" F.pp c (prettier valid_mode) ty (pplist (fun fmt (_,x)-> Format.fprintf fmt "%a" (prettier valid_mode) x) ", ") alltys in
  error_msg_mode ~loc !valid_mode msg
  
let error_overloaded_app_tgt ~valid_mode ~loc ~ety c =
  let msg = Format.asprintf "@[<v>%a is overloaded but none of its types matches make it build a term of type @[<hov>%a@]@]" F.pp c (prettier valid_mode) ety in
  error_msg_mode ~loc !valid_mode msg


let error_not_poly ~loc c ty sk =
  error ~loc (Format.asprintf "@[<hv>this rule imposes on %a the type@ %a@ is less general than the declared one@ %a@]"
    F.pp c
    pretty_ty ty
    pretty_ty sk)

type ret = TypeAssignment.t MutableOnce.t TypeAssignment.t_
[@@deriving show]
type ret_id = IdPos.t * TypeAssignment.t MutableOnce.t TypeAssignment.t_
[@@deriving show]
type spilled_phantoms = ScopedTerm.t list
[@@deriving show]
type sigma = { ty : TypeAssignment.t; nocc : int; loc : Loc.t }
[@@deriving show]
type ctx = { ret : ret; mode : TypeAssignment.tmode }
[@@deriving show]

let mk_uvar =
  let i = ref 0 in
  fun s -> incr i; TypeAssignment.UVar(MutableOnce.make (F.from_string (s ^ string_of_int !i)))

let local_type ctx ~loc (lang,c,_) : ret_id TypeAssignment.overloading =
  let lang = match lang with Scope.Bound c -> c | _ -> assert false in
  try TypeAssignment.Single (Scope.dummy_type_decl_id, (Scope.Map.find (c,lang) ctx).ret) (* local types have no id, 0 is given by default *)
  with Not_found -> anomaly ~loc "free variable"

let global_type unknown_global env ~loc c : ret_id TypeAssignment.overloading =
  try TypeAssignment.fresh_overloaded @@ F.Map.find c env
  with Not_found ->
    try
      let ty,id,_ = F.Map.find c !unknown_global in
      Single (id,TypeAssignment.unval ty)
    with Not_found ->
      let ty = TypeAssignment.Val (mk_uvar (Format.asprintf "Unknown_type_of_%a_" F.pp c)) in
      let id = Scope.fresh_type_decl_id loc in
      unknown_global := F.Map.add c (ty,id,loc) !unknown_global;
      Single (id,TypeAssignment.unval ty)


type classification =
  | Simple of { srcs : (TypeAssignment.tmode * ret) list; tgt : ret }
  | Variadic of { srcs : ret list; tgt : ret }
  | Unknown

let prop = TypeAssignment.Prop Relation

let rec classify_arrow = function
  | TypeAssignment.Arr(_(*TODO: @FissoreD*),Variadic,x,tgt) -> Variadic { srcs = [x]; tgt }
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

let check ~is_rule ~type_abbrevs ~kinds ~types:env ~unknown (t : ScopedTerm.t) ~(exp : TypeAssignment.t) =
  let valid_mode = ref true in

  (* Format.eprintf "============================ checking %a\n" ScopedTerm.pretty t; *)
  let sigma : sigma F.Map.t ref = ref F.Map.empty in
  let unknown_global = ref unknown in
  let fresh_name = let i = ref 0 in fun () -> incr i; F.from_string ("%dummy"^ string_of_int !i) in
  (* let set_fresh_id = let i = ref 0 in fun x -> incr i; x := Some !i in *)

  let global_type = global_type unknown_global in

  let get_type ~loc ctx env (scope, c, _ as t) =
    match scope with
    | Scope.Global _ -> global_type env ~loc c
    | Bound lang -> local_type ctx ~loc t
  in

  let rec check ~positive (ctx : ctx Scope.Map.t) ~loc ~tyctx x ety : spilled_phantoms =
    (* Format.eprintf "@[<hov 2>checking %a : %a@]\n" ScopedTerm.pretty_ x TypeAssignment.pretty_mut_once ety; *)
    match x with
    | Impl(b,t1,t2) -> check_impl ~positive ctx ~loc ~tyctx b t1 t2 ety
    | Const(Global _,_,_ as c) -> check_global ctx ~loc ~tyctx c ety
    | Const(Bound _,_,_ as c) -> check_local ctx ~loc ~tyctx c ety
    | CData c -> check_cdata ~loc ~tyctx kinds c ety
    | Spill(_,{contents = Phantom _}) -> assert false
    | Spill(sp,info) -> check_spill ~positive ctx ~loc ~tyctx sp info ety
    | App((gid,_,_ as hd),x,xs) -> check_app ~positive ctx ~loc ~tyctx hd (get_type ~loc ctx env hd) (x::xs) ety 
    | Lam(c,cty,t) -> check_lam ~positive ctx ~loc ~tyctx c cty t ety
    | Discard -> []
    | Var((_,c,_ as hd),args) -> check_app ~positive ctx ~loc ~tyctx hd (uvar_type ~loc c) args ety
    | Cast(t,ty) ->
        let ty = TypeAssignment.subst (fun f -> Some (UVar(MutableOnce.make f))) @@ check_loc_tye ~type_abbrevs ~kinds F.Set.empty ty in
        let spills = check_loc ~positive ctx ~tyctx:None t ~ety:ty in
        if unify ty ety then spills
        else error_bad_ety ~valid_mode ~loc ~tyctx ScopedTerm.pretty_ x ty ~ety

  and resolve_gid ~loc id gid ety ty =
    if not @@ MutableOnce.is_set ty then MutableOnce.set ~loc ty (TypeAssignment.Val ety);
    match gid with
    | Scope.Global x -> x.decl_id <- id
    | _ -> ()

  and check_impl ~positive ctx ~loc ~tyctx b t1 t2 ety =
    if not @@ unify (ety) prop then error_bad_ety ~valid_mode ~loc ~tyctx ~ety:prop ScopedTerm.pretty_ (Impl(b,t1,t2)) (ety)
    else
      let lhs, rhs,c (* of => *) = if b then t1,t2,F.implf else t2,t1,F.rimplf in
      let spills = check_loc ~positive ~tyctx:(Some c) ctx rhs ~ety:prop in
      let lhs_ty = mk_uvar "Src" in
      let more_spills = check_loc ~positive:(not positive) ~tyctx:None ctx ~ety:lhs_ty lhs in
      let ety1 = prop in
      let ety2 = TypeAssignment.App(F.from_string "list",prop,[]) in
      if try_unify lhs_ty ety1 then spills @ more_spills (* probably an error if not empty *)
      else if unify lhs_ty (ety2) then spills @ more_spills (* probably an error if not empty *)
      else error_bad_ety2 ~valid_mode ~tyctx:(Some c) ~loc ~ety1 ~ety2  ScopedTerm.pretty lhs lhs_ty

  and check_global ctx ~loc ~tyctx (gid,c,tya) ety =
    match global_type env ~loc c with
    | Single (id,ty) ->
        if unify ty ety then (resolve_gid ~loc id gid ety tya; [])
        else error_bad_ety ~valid_mode ~tyctx ~loc ~ety F.pp c ty
    | Overloaded l ->
        if unify_first ~loc gid l ety tya then []
        else error_bad_const_ety_l ~valid_mode ~tyctx ~loc ~ety c l

  and check_local ctx ~loc ~tyctx (_,c,tya as t) ety =
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

  and check_lam ~positive ctx ~loc ~tyctx sc cty t ety =
    let name_lang, c, tya = match sc with Some c -> c | None -> mk_ty_name elpi_language (fresh_name ()) in
    let set_tya_ret f = MutableOnce.set ~loc tya (Val f); f in
    let src = set_tya_ret @@ match cty with
      | None -> mk_uvar "Src"
      | Some x -> TypeAssignment.subst (fun f -> Some (UVar(MutableOnce.make f))) @@ check_loc_tye ~type_abbrevs ~kinds F.Set.empty x
    in 
    (* Format.eprintf "Ty is setted to %a@." (MutableOnce.pp TypeAssignment.pp) (tya); *)
    let tgt = mk_uvar "Tgt" in
    (* let () = Format.eprintf "lam ety %a\n" TypeAssignment.pretty ety in *)
    let mode = TypeAssignment.MRef (MutableOnce.make F.dummyname) in
    if unify (TypeAssignment.Arr(mode, Ast.Structured.NotVariadic,src,tgt)) ety then
      (* let () = Format.eprintf "add to ctx %a : %a\n" F.pp name TypeAssignment.pretty src in *)
      check_loc ~positive ~tyctx (Scope.Map.add (c,name_lang) { ret = src; mode } ctx) t ~ety:tgt
    else
      error_bad_function_ety ~valid_mode ~loc ~tyctx ~ety sc t

  and check_spill ~positive(*TODO*) ctx ~loc ~tyctx sp info ety =
    let inner_spills = check_spill_conclusion_loc ~positive ~tyctx:None ctx sp ~ety:(TypeAssignment.(Arr(MRef (MutableOnce.make F.dummyname), Ast.Structured.NotVariadic,ety,mk_uvar "Spill"))) in
    assert(inner_spills = []);
    let phantom_of_spill_ty i ty =
      { loc; it = Spill(sp,ref (Phantom(i+1))); ty = MutableOnce.create (TypeAssignment.Val ty) } in
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

  and check_app ~positive ctx ~loc ~tyctx (cid,c,tya) cty args ety =
    match cty with
    | Overloaded l ->
      (* Format.eprintf "@[options %a %a %d:@ %a@]\n" F.pp c TypeAssignment.pretty_mut_once ety (List.length args) (pplist (fun fmt (_,x) -> TypeAssignment.pretty_mut_once fmt x) "; ") l; *)
      let l = List.filter (unify_tgt_ety (List.length args) ety) l in
      begin match l with
      | [] -> error_overloaded_app_tgt ~valid_mode ~loc ~ety c
      | [ty] -> 
      (* Format.eprintf "1option left: %a\n" TypeAssignment.pretty (snd ty); *)
        check_app ~positive ctx ~loc ~tyctx (cid,c,tya) (Single ty) args ety
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
          else error_bad_ety ~valid_mode ~loc ~tyctx ~ety ScopedTerm.pretty_ (App(mk_ty_name (Scope.mkGlobal ~escape_ns:true ()(* sucks *)) c,List.hd args,List.tl args)) ty in
        let monodirectional () =
          (* Format.eprintf "checking app mono %a\n" F.pp c; *)
          let tgt = check_app_single ~positive ctx ~loc (c,cid,tya) ty [] args in
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
            let _ = check_app_single ~positive ctx ~loc (c,cid,tya) ty [] args in (resolve_gid ~loc id cid ty tya; [])
          else err rest_tgt in
        match classify_arrow ty with
        | Unknown | Variadic _ -> monodirectional ()
        | Simple { srcs; tgt } ->
          if List.length args > List.length srcs then monodirectional () (* will error *)
          else
            if any_arg_is_spill args then monodirectional ()
            else bidirectional srcs tgt

  (* REDO PROCESSING ONE SRC at a time *)
  and check_app_overloaded ~positive ctx ~loc (c, cid, tya as c_w_id) ety args targs alltys = function
    | [] -> error_overloaded_app ~valid_mode ~loc c args ~ety alltys
    | (id,t)::ts ->
        (* Format.eprintf "checking overloaded app %a\n" F.pp c; *)
        let decore_with_dummy_mode =  List.map (fun x -> (TypeAssignment.MRef (MutableOnce.make F.dummyname),x)) in
        match classify_arrow t with
        | Unknown -> error ~loc (Format.asprintf "Type too ambiguous to be assigned to the overloaded constant: %s for type %a" (F.show c) pretty_ty t)
        | Simple { srcs; tgt } ->
          (* Format.eprintf "argsty : %a\n" TypeAssignment.pretty (arrow_of_tys targs ety); *)
            if try_unify (arrow_of_tys srcs tgt) (arrow_of_tys (decore_with_dummy_mode targs) ety) then (resolve_gid ~loc id cid t tya;[]) (* TODO: here we should something ? *)
            else check_app_overloaded ~positive ctx ~loc c_w_id ety args targs alltys ts
        | Variadic { srcs ; tgt } ->
            let srcs = extend srcs targs |> decore_with_dummy_mode in
            if try_unify (arrow_of_tys srcs tgt) (arrow_of_tys (decore_with_dummy_mode targs) ety) then (resolve_gid ~loc id cid t tya;[]) (* TODO: here we should something ? *)
            else check_app_overloaded ~positive ctx ~loc c_w_id ety args targs alltys ts

  and infer_mode ctx m { loc; it } =
    match it with
    | Const(Scope.Bound l,f,ty) ->
        begin match Scope.Map.find_opt (f,l) ctx with
        | None ->  anomaly "unbound"
        | Some info ->
            if TypeAssignment.is_tmode_set info.mode || unif_mode false info.mode m then ()
            else error ~loc ("mode mismatch on bound variable " ^ F.show f)
      end
    | _ -> ()

  and check_app_single ~positive ctx ~loc (c,_,_ as fc) ty consumed args =
    match args with
    | [] -> ty
    | x :: xs ->
      (* Format.eprintf "@[<h>Checking term %a with type %a@]@." ScopedTerm.pretty x TypeAssignment.pretty_mut_once_raw ty; *)
      (* Format.eprintf "checking app %a against %a@." ScopedTerm.pretty_ (ScopedTerm.App(snd c, fst c,x,xs)) TypeAssignment.pretty_mut_once_raw ty; *)
      match ty with
        | TypeAssignment.Arr(_(*TODO: @FissoreD*), Variadic,s,t) ->
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
    | Impl(true,x,y) ->
        let lhs = mk_uvar "LHS" in
        let spills = check_loc ~positive ~tyctx ctx x ~ety:lhs in
        if spills <> [] then error ~loc "Hard spill";
        if try_unify lhs prop || try_unify lhs (App(F.from_string "list",prop,[]))
        then check_spill_conclusion_loc ~positive ~tyctx ctx y ~ety
        else error ~loc "Bad impl in spill"
    | App((Global _,c,_ as sc),x,xs) when F.equal c F.andf ->
        let spills = check_loc ~positive ~tyctx ctx x ~ety:prop in
        if spills <> [] then error ~loc "Hard spill";
        begin match xs with
        | [] -> assert false
        | [x] -> check_loc ~positive ~tyctx ctx x ~ety
        | x::xs -> check_spill_conclusion ~positive ~tyctx ctx ~loc (App(sc,x,xs)) ety
        end
    | _ -> check ~positive ~tyctx ctx ~loc it ety

  and check_matches_poly_skema_loc ~unknown { loc; it } =
    let c, args =
      let rec head it =
        match it with
        | App((Global _,f,_),{ it = Lam(_,_,x) },[]) when F.equal F.pif f -> head x.it
        | Impl(false,{ it = App((Global _,c',_),x,xs) },_) -> c', x :: xs
        | Impl(false,{ it = Const((Global _,c',_)) },_) -> c', []
        | App((Global _,c,_),x,xs) -> c, x :: xs
        | Const((Global _,c,_)) -> c, []
        | _ ->
          (* Format.eprintf "%a" ScopedTerm.pretty_ it; *)
          assert false in
      head it in
    (* Format.eprintf "Checking %a\n" F.pp c; *)
    match F.Map.find c env with
    | Single (_id,Ty _) -> () (* TODO: Should use id? *)
    | Single (_id, Lam _ as sk) -> check_matches_poly_skema ~loc ~pat:(TypeAssignment.fresh sk) c (arrow_of_args args prop) (* TODO: should use id? *)
    | Overloaded _ -> ()
    | exception Not_found -> assert(F.Map.mem c unknown)

  and check_matches_poly_skema ~loc ~pat c ty =
    if try_matching ~pat ty then () else error_not_poly ~loc c ty (fst pat |> snd)

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
    
  and unify_first ~loc gid l ety tya =
    let vars = TypeAssignment.vars_of (Val ety) in
    let rec aux = function
      | [] -> false
      | (id, x)::xs -> if unify x ety then (resolve_gid ~loc id gid ety tya; true) else (undo vars; aux xs)
    in
      aux l

  and undo ((l_ty : TypeAssignment.t MutableOnce.t list), (l_m : TypeAssignment.tmode MutableOnce.t list)) =
    List.iter MutableOnce.unset l_ty;
    List.iter MutableOnce.unset l_m

  and unif_mode matching m1 m2 =
    let m1, m2 = TypeAssignment.(deref_tmode m1, deref_tmode m2) in
    match m1, m2 with
    | MVal m1, MVal m2 -> m1 = m2
    | MRef _, MVal _ when matching -> false
    | MRef m1, MRef m2 when m1 == m2 -> true
    | MRef m1, _ -> MutableOnce.set m1 m2; true
    | _, MRef m2 -> MutableOnce.set m2 m1; true

  and uvar_type ~loc c =
    try
      let { ty; nocc } as info = F.Map.find c !sigma in
      sigma := F.Map.add c { info with nocc = nocc+1 } !sigma;
      Single (Scope.dummy_type_decl_id, TypeAssignment.unval @@ ty)
    with Not_found ->
      let ty = TypeAssignment.UVar (MutableOnce.make c) in
      sigma := F.Map.add c { ty = TypeAssignment.Val ty; nocc = 1; loc } !sigma;
      Single (Scope.dummy_type_decl_id, ty)
  (* matching=true -> X = t fails (X = Y works)*)
  and unif ~matching t1 t2 =
    (* Format.eprintf "%a = %a\n" TypeAssignment.pretty_mut_once_raw t1 TypeAssignment.pretty_mut_once_raw t2; *)
    let open TypeAssignment in
    match t1, t2 with
    | Any, _ -> true
    | _, Any -> true
    | UVar m, _ when MutableOnce.is_set m -> unif ~matching (TypeAssignment.deref m) t2
    | _, UVar m when MutableOnce.is_set m -> unif ~matching t1 (TypeAssignment.deref m)
    | App(c1,x,xs), App(c2,y,ys) when F.equal c1 c2 ->
        unif ~matching x y && Util.for_all2 (unif ~matching) xs ys
    | Cons c1, Cons c2 when F.equal c1 c2 -> true
    | Prop _, Prop _ -> true (* unification of prop is correct for tc indipendently of their functionality *)
    | Arr(m1,b1,s1,t1), Arr(m2,b2,s2,t2) -> 
      valid_mode := unif_mode matching m1 m2;
      !valid_mode && b1 == b2 && unif ~matching s1 s2 && unif ~matching t1 t2
    | Arr(_,Variadic,_,t), _ -> unif ~matching t t2 (* TODO *)
    | _, Arr(_,Variadic,_,t) -> unif ~matching t1 t (* TODO *)
    | UVar m, UVar n when matching -> assign m t2 (* see disjoint *)
    | UVar m, _ when not matching -> assign m t2
    | _, UVar m -> assign m t1
    | Cons c, _ when F.Map.mem c type_abbrevs ->
        let t1 = apply (fst @@ F.Map.find c type_abbrevs) [] in
        unif ~matching t1 t2
    | _, Cons c when F.Map.mem c type_abbrevs ->
        let t2 = apply (fst @@ F.Map.find c type_abbrevs) [] in
        unif ~matching t1 t2
    | App(c,x,xs), _ when F.Map.mem c type_abbrevs ->
        let t1 = apply (fst @@ F.Map.find c type_abbrevs) (x::xs) in
        unif ~matching t1 t2
    | _, App(c,x,xs) when F.Map.mem c type_abbrevs ->
        let t2 = apply (fst @@ F.Map.find c type_abbrevs) (x::xs) in
        unif ~matching t1 t2
    | _,_ -> false

  and unify (x: TypeAssignment.t MutableOnce.t TypeAssignment.t_) (y: TypeAssignment.t MutableOnce.t TypeAssignment.t_) = unif ~matching:false x y
  and try_matching ~pat:((_,x),vars) y =
    let vars = F.Map.bindings vars |> List.map snd |> List.map cell_of, [] in
    let deref x = cell_of (TypeAssignment.deref x) in
    if unif ~matching:true x y then
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

    let spills = check_loc ~positive:true ~tyctx:None Scope.Map.empty t ~ety:(TypeAssignment.unval exp) in
    if is_rule then check_matches_poly_skema_loc ~unknown:!unknown_global t;
    if spills <> [] then error ~loc:t.loc "cannot spill in head";
    F.Map.iter (fun k { nocc = n; loc } ->
      if n = 1 && not @@ silence_linear_warn k then
        warn ~loc (Format.asprintf "%a is linear: name it _%a (discard) or %a_ (fresh variable)"
        F.pp k F.pp k F.pp k))
      !sigma;
    !unknown_global

let check1_undeclared w f (t, id, loc) =
  match TypeAssignment.is_monomorphic t with
  | None -> error ~loc Format.(asprintf "@[Unable to infer a closed type for %a:@ %a@]" F.pp f pretty_ty (TypeAssignment.unval t))
  | Some ty ->
      if not @@ Re.Str.(string_match (regexp "^\\(.*aux[0-9']*\\|main\\)$") (F.show f) 0) then
        w := Format.((f, loc), asprintf "type %a %a." F.pp f pretty_ty (TypeAssignment.unval t)) :: !w;
      TypeAssignment.Single (id, ty)

let check_undeclared ~unknown =
  let w = ref [] in
  let env = F.Map.mapi (check1_undeclared w) unknown in
  if !w <> [] then begin
    let undeclared, types = List.split !w in
    warn Format.(asprintf "@[<v>Undeclared globals:@ @[<v>%a@].@ Please add the following text to your program:@\n%a@]" (pplist (fun fmt (f,loc) -> Format.fprintf fmt "- %a %a" Loc.pp loc F.pp f) ", ") undeclared
     (pplist pp_print_string "") types);
  end;
  env

(* let check ~type_abbrevs a b c =
  try check ~type_abbrevs a b c with
  | CompileError(_,"Unknown global: %spill") -> Printf.eprintf "SPILLING"; exit 1
  | CompileError(_,s) when Re.Str.(string_match (regexp "Unknown global: @")) s 0 -> Printf.eprintf "MACRO"; exit 1
  | CompileError(loc,msg) -> Format.eprintf "Ignoring type error: %a %s\n" (Util.pp_option Loc.pp) loc msg; TypeAssignment.(Val Prop) *)
