open Elpi_util
open Elpi_parser
open Elpi_runtime
open Util
module F = Ast.Func

module IdPos : sig 
  type t [@@deriving show,ord]
  module Map : Map.S with type key = t
  module Set : Set.S with type elt = t

  val make_loc : Loc.t -> t
  val make_str : string -> t
end = struct
  include Loc
  module Map = Map.Make(Loc)
  module Set = Set.Make(Loc)
  let make_loc loc = loc
  let make_str str = make_loc (Loc.initial str)
end

module Scope = struct

  type language = string
  [@@ deriving show, ord]

  type type_decl_id = IdPos.t
  [@@ deriving show, ord]
  let dummy_type_decl_id = IdPos.make_str "dummy"
  let fresh_type_decl_id loc = (IdPos.make_loc loc)
  let is_dummy_type_decl_id x = x <= 0

  type t =
    | Bound  of language (* bound by a lambda, stays bound *)
    | Global of {
        escape_ns : bool; (* when true name space elimination does not touch this constant *)
        mutable decl_id : type_decl_id;
      }
  [@@ deriving show, ord]

  module Map = Map.Make(struct
    type t = F.t * language
    [@@ deriving show, ord]
  end)
  module Set = Set.Make(struct
    type t = F.t * language
    [@@ deriving show, ord]
  end)

  let mkGlobal ?(escape_ns=false) ?(decl_id = dummy_type_decl_id) () =
    Global { escape_ns ; decl_id }

end
let elpi_language : Scope.language = "lp"

module ScopeContext = struct


type ctx = { vmap : (Scope.language * F.t * F.t) list; uvmap : (F.t * F.t) list ref }
let empty () = { vmap = []; uvmap = ref [] }

let eq_var { vmap } language c1 c2 = List.mem (language,c1,c2) vmap


let purge language f c l = List.filter (fun (l,x,y) -> l = language && not @@ F.equal (f (x,y)) c) l
let push_ctx language c1 c2 ctx = { ctx with vmap = (language,c1 , c2) :: (purge language fst c1 @@ purge language snd c2 ctx.vmap) }
let eq_uvar ctx c1 c2 =
  if List.exists (fun (x,_) -> F.equal x c1) !(ctx.uvmap) ||
     List.exists (fun (_,y) -> F.equal y c2) !(ctx.uvmap) then
    List.mem (c1,c2) !(ctx.uvmap)
  else begin
    ctx.uvmap := (c1,c2) :: !(ctx.uvmap);
    true
  end
end


module ScopedTypeExpression = struct
  open ScopeContext

  module SimpleType = struct
    type t_ =
    | Any
    | Con of F.t
    | App of F.t * t * t list
    | Arr of t * t
    and t = { it : t_; loc : Loc.t }
    [@@ deriving show]

  end

  type t_ =
    | Any
    | Const of Scope.t * F.t
    | App of F.t * e * e list
    | Arrow of Ast.Structured.variadic * e * e
    | Pred of Ast.Structured.functionality * (Ast.Mode.t * e) list
  and e = { it : t_; loc : Loc.t }
  [@@ deriving show]


  open Format

  let arrs = 0
  let app = 1

  let lvl_of = function
    | Arrow _ | Pred _ -> arrs
    | App _ -> app
    | _ -> 2

  let rec pretty_e fmt = function
    | Any -> fprintf fmt "any"
    | Const(_,c) -> F.pp fmt c
    | App(f,x,xs) -> fprintf fmt "@[<hov 2>%a@ %a@]" F.pp f (Util.pplist (pretty_e_parens ~lvl:app) " ") (x::xs)
    | Arrow(NotVariadic,s,t) -> fprintf fmt "@[<hov 2>%a ->@ %a@]" (pretty_e_parens ~lvl:arrs) s pretty_e_loc t
    | Arrow(Variadic,s,t) -> fprintf fmt "%a ..-> %a" (pretty_e_parens ~lvl:arrs) s pretty_e_loc t
    | Pred(_,[]) -> fprintf fmt "prop"
    | Pred(_,l) -> fprintf fmt "pred %a" (Util.pplist pretty_ie ", ") l
  and pretty_ie fmt (i,e) =
    fprintf fmt "%s:%a" (match i with Ast.Mode.Input -> "i" | Output -> "o") pretty_e_loc e
  and pretty_e_parens ~lvl fmt = function
    | t when lvl >= lvl_of t.it -> fprintf fmt "(%a)" pretty_e_loc t
    | t -> pretty_e_loc fmt t
  and pretty_e_loc fmt { it } = pretty_e fmt it
  let pretty_e fmt (t : e) = Format.fprintf fmt "@[%a@]" pretty_e_loc t


  let rec of_simple_type = function
    | SimpleType.Any -> Any
    | Con c -> Const(Scope.mkGlobal (),c)
    | App(c,x,xs) -> App(c,of_simple_type_loc x,List.map of_simple_type_loc xs)
    | Arr(s,t) -> Arrow(NotVariadic,of_simple_type_loc s, of_simple_type_loc t)
  and of_simple_type_loc { it; loc } = { it = of_simple_type it; loc }

  type v_ =
    | Lam of F.t * v_
    | Ty of e
  [@@ deriving show]

  type t = { name : F.t; value : v_; nparams : int; loc : Loc.t; indexing : Ast.Structured.tattribute option }
  [@@ deriving show]

  let rec eqt ctx t1 t2 =
    match t1.it, t2.it with
    | Const(Global _ as b1,c1), Const(Global _ as b2,c2) -> Scope.compare b1 b2 == 0 && F.equal c1 c2
    | Const(Bound l1,c1), Const(Bound l2,c2) -> Scope.compare_language l1 l2 == 0 && eq_var ctx l1 c1 c2
    | App(c1,x,xs), App(c2,y,ys) -> F.equal c1 c2 && eqt ctx x y && Util.for_all2 (eqt ctx) xs ys
    | Arrow(b1,s1,t1), Arrow(b2,s2,t2) -> b1 = b2 && eqt ctx s1 s2 && eqt ctx t1 t2
    | Pred(f1,l1), Pred(f2,l2) -> f1 = f2 && Util.for_all2 (fun (m1,t1) (m2,t2) -> Ast.Mode.compare m1 m2 == 0 && eqt ctx t1 t2) l1 l2
    | Any, Any -> true
    | _ -> false

  let rec eq ctx t1 t2 =
    match t1, t2 with
    | Lam(c1,b1), Lam(c2,b2) -> eq (push_ctx "lp" c1 c2 ctx) b1 b2
    | Ty t1, Ty t2 -> eqt ctx t1 t2
    | _ -> false

  let equal { name = n1; value = x } { name = n2; value = y } = F.equal n1 n2 && eq (empty ()) x y

  let compare _ _ = assert false

  let rec smart_map_scoped_loc_ty f ({ it; loc } as orig) =
    let it' = smart_map_scoped_ty f it in
    if it' == it then orig else { it = it'; loc }
  and smart_map_scoped_ty f orig =
    match orig with
    | Any -> orig
    | Const((Scope.Bound _| Scope.Global { escape_ns = true }),_) -> orig
    | Const(Scope.Global _ as g,c) ->
        let c' = f c in
        if c == c' then orig else Const(g,c')
    | App(c,x,xs) ->
        let c' = f c in
        let x' = smart_map_scoped_loc_ty f x in
        let xs' = smart_map (smart_map_scoped_loc_ty f) xs in
        if c' == c && x' == x && xs' == xs then orig else App(c',x',xs')
    | Arrow(v,x,y) ->
        let x' = smart_map_scoped_loc_ty f x in
        let y' = smart_map_scoped_loc_ty f y in
        if x' == x && y' == y then orig else Arrow(v,x',y')
    | Pred(c,l) ->
        let l' = smart_map (fun (m,x as orig) ->
          let x' = smart_map_scoped_loc_ty f x in
          if x' == x then orig else m,x') l in
        if l' == l then orig else Pred(c,l')

  let rec smart_map_tye f = function
    | Lam(c,t) as orig ->
        let t' = smart_map_tye f t in
        if t == t' then orig else Lam(c,t')
    | Ty t as orig ->
      let t' = smart_map_scoped_loc_ty f t in
      if t == t' then orig else Ty t'

  let smart_map f ({ name; value; nparams; loc; indexing } as orig) =
    let name' = f name in
    let value' = smart_map_tye f value in
    if name == name' && value' == value then orig
    else { name = name'; value = value'; nparams; loc; indexing }

end

module MutableOnce : sig 
  type 'a t
  [@@ deriving show]
  val make : F.t -> 'a t
  val create : 'a -> 'a t
  val set : 'a t -> 'a -> unit
  val unset : 'a t -> unit
  val get : 'a t -> 'a
  val get_name : 'a t -> F.t
  val is_set : 'a t -> bool
  val pretty : Format.formatter -> 'a t -> unit
end = struct
  type 'a t = F.t * 'a option ref
  [@@ deriving show]

  let make f = f, ref None

  let create t = F.from_string "_", ref (Some t)

  let is_set (_,x) = Option.is_some !x
  let set (_,r) x =
    match !r with
    | None -> r := Some x
    | Some _ -> anomaly "MutableOnce"
  
  let get (_,x) = match !x with Some x -> x | None -> anomaly "get"
  let get_name (x,_) = x
  let unset (_,x) = x := None

  let pretty fmt (f,x) =
    match !x with
    | None -> Format.fprintf fmt "%a" F.pp f
    | Some _ -> anomaly "pp"
end

module TypeAssignment = struct

  type 'a overloading =
    | Single of 'a
    | Overloaded of 'a list
  [@@ deriving show, fold, iter]

  type 'a t_ =
    | Prop | Any
    | Cons of F.t
    | App of F.t * 'a t_ * 'a t_ list
    | Arr of Ast.Structured.variadic * 'a t_ * 'a t_
    | UVar of 'a
  [@@ deriving show, fold, ord]

  type skema = Lam of F.t * skema | Ty of F.t t_
  [@@ deriving show, ord]
  type overloaded_skema = skema overloading
  [@@ deriving show]

  type skema_w_id = IdPos.t * skema
  [@@ deriving show, ord]
  type overloaded_skema_with_id = skema_w_id overloading
  [@@ deriving show]

  type t = Val of t MutableOnce.t t_
  [@@ deriving show]

  let nparams (_,t : skema_w_id) =
      let rec aux = function Ty _ -> 0 | Lam(_,t) -> 1 + aux t in
      aux t
  
  let rec subst map = function
    | (Prop | Any | Cons _) as x -> x
    | App(c,x,xs) -> App (c,subst map x,List.map (subst map) xs)
    | Arr(v,s,t) -> Arr(v,subst map s, subst map t)
    | UVar c ->
        match map c with
        | Some x -> x
        | None -> anomaly "TypeAssignment.subst"

  let fresh ((id,sk): skema_w_id) =
    let rec fresh map = function
      | Lam(c,t) -> fresh (F.Map.add c (UVar (MutableOnce.make c)) map) t
      | Ty t -> if F.Map.is_empty map then (id, Obj.magic t), map else (id, subst (fun x -> F.Map.find_opt x map) t), map
  in
    fresh F.Map.empty sk

  let fresh_overloaded = function
    | Single sk -> Single (fst @@ fresh sk)
    | Overloaded l -> Overloaded (List.map (fun x -> fst @@ fresh x) l)

  let rec apply m sk args =
    match sk, args with
    | Ty t, [] -> if F.Map.is_empty m then Obj.magic t else subst (fun x -> F.Map.find_opt x m) t
    | Lam(c,t), x::xs -> apply (F.Map.add c x m) t xs
    | _ -> assert false (* kind checker *)

  let apply (_,sk:skema_w_id) args = apply F.Map.empty sk args

  let eq_skema_w_id (_,x) (_,y) = compare_skema x y = 0
  let diff_id_check ((id1:IdPos.t),_) (id2,_) = assert (id1<>id2)
  let diff_ids_check e = List.iter (diff_id_check e)

  let rec remove_mem e acc = function
    | [] -> List.rev acc
    | x::xs when eq_skema_w_id e x ->
      diff_ids_check x xs;
      List.rev_append acc xs
    | x::xs -> remove_mem e (x::acc) xs

  let rec merge_skema t1 t2 =
    match t1, t2 with
    | Single x, Single y when eq_skema_w_id x y -> t1
    | Single x, Single y -> diff_id_check x y; Overloaded [x;y]
    | Single x, Overloaded ys  -> Overloaded (x :: remove_mem x [] ys)
    | Overloaded xs, Single y when List.exists (eq_skema_w_id y) xs -> t1
    | Overloaded xs, Single y -> diff_ids_check y xs; Overloaded(xs@[y])
    | Overloaded xs, Overloaded _ ->
        List.fold_right (fun x -> merge_skema (Single x)) xs t2
  
  let unval (Val x) = x
  let rec deref m =
    match unval @@ MutableOnce.get m with
    | UVar m when MutableOnce.is_set m -> deref m
    | x -> x

  let set m v = MutableOnce.set m (Val v)

  exception Not_monomorphic
  let is_monomorphic (Val t) =
    let rec map = function
      | UVar r when MutableOnce.is_set r -> map (deref r)
      | UVar _ -> raise Not_monomorphic
      | Prop -> Prop
      | Any -> Any
      | Cons c -> Cons c
      | App(c,x,xs) -> App(c,map x, List.map map xs)
      | Arr(b,s,t) -> Arr(b,map s,map t)
    in
    try 
      let t = map t in
      Some (Ty (Obj.magic t : F.t t_)) (* No UVar nodes *)
    with Not_monomorphic -> None
  
  let rec is_arrow_to_prop = function
    | Prop -> true
    | Any | Cons _ | App _ -> false
    | Arr(_,_,t) -> is_arrow_to_prop t
    | UVar _ -> false

  let rec is_predicate = function
    | Lam (_,t) -> is_predicate t
    | Ty t -> is_arrow_to_prop t

  let is_predicate = function
    | Single (_,t) -> is_predicate t
    | Overloaded l -> List.exists (fun (_,x) -> is_predicate x) l

  open Format

  let arrs = 0
  let app = 1

  let lvl_of = function
    | Arr _ -> arrs
    | App _ -> app
    | _ -> 2

  let rec pretty fmt = function
    | Prop -> fprintf fmt "prop"
    | Any -> fprintf fmt "any"
    | Cons c -> F.pp fmt c
    | App(f,x,xs) -> fprintf fmt "@[<hov 2>%a@ %a@]" F.pp f (Util.pplist (pretty_parens ~lvl:app) " ") (x::xs)
    | Arr(NotVariadic,s,t) -> fprintf fmt "@[<hov 2>%a ->@ %a@]" (pretty_parens ~lvl:arrs) s pretty t
    | Arr(Variadic,s,t) -> fprintf fmt "%a ..-> %a" (pretty_parens ~lvl:arrs) s pretty t
    | UVar m when MutableOnce.is_set m -> pretty fmt @@ deref m
    | UVar m -> MutableOnce.pretty fmt m
  and pretty_parens ~lvl fmt = function
    | UVar m when MutableOnce.is_set m -> pretty_parens ~lvl fmt @@ deref m
    | t when lvl >= lvl_of t -> fprintf fmt "(%a)" pretty t
    | t -> pretty fmt t
  let pretty fmt t = Format.fprintf fmt "@[%a@]" pretty t

  let vars_of (Val t)  = fold_t_ (fun xs x -> if MutableOnce.is_set x then xs else x :: xs) [] t

end

module ScopedTerm = struct
  open ScopeContext

  (* User Visible *)
  module SimpleTerm = struct
    type t_ =
      | Impl of bool * t * t (* `Impl(true,t1,t2)` ≡ `t1 => t2` and `Impl(false,t1,t2)` ≡ `t1 :- t2` *)
      | Const of Scope.t * F.t
      | Discard
      | Var of F.t * t list
      | App of Scope.t * F.t * t * t list
      | Lam of (F.t * Scope.language) option * ScopedTypeExpression.SimpleType.t option * t
      | Opaque of CData.t
      | Cast of t * ScopedTypeExpression.SimpleType.t
    and t = { it : t_; loc : Loc.t }
   [@@ deriving show]

   type constant = int
   let mkGlobal ~loc c = { loc; it = Const(Scope.mkGlobal ~escape_ns:true (),F.from_string @@ Constants.Map.find c Data.Global_symbols.table.c2s) }
   let mkBound ~loc ~language n = { loc; it = Const(Bound language,n)}
   let mkAppGlobal ~loc c x xs = { loc; it = App(Scope.mkGlobal ~escape_ns:true (),F.from_string @@ Constants.Map.find c Data.Global_symbols.table.c2s,x,xs) }
   let mkAppBound ~loc ~language n x xs = { loc; it = App(Bound language,n,x,xs) }
   let mkVar ~loc n l = { loc; it = Var(n,l) }
   let mkOpaque ~loc o = { loc; it = Opaque o }
   let mkCast ~loc t ty = { loc; it = Cast(t,ty) }
   let mkDiscard ~loc = { loc; it = Discard }
   let mkLam ~loc n ?ty t =  { loc; it = Lam(n,ty,t)  }
   let mkImplication ~loc s t = { loc; it = Impl(true,s,t) }
   let mkPi ~loc n ?ty t = { loc; it = App(Scope.mkGlobal ~escape_ns:true (),F.pif,{ loc; it = Lam (Some (n,elpi_language),ty,t) },[]) }
   let mkConj ~loc = function
     | [] -> { loc; it = Const(Scope.mkGlobal ~escape_ns:true (), F.truef) }
     | [x] -> x
     | x :: xs -> { loc; it = App(Scope.mkGlobal ~escape_ns:true (), F.andf, x, xs)}
    let mkEq ~loc a b = { loc; it = App(Scope.mkGlobal ~escape_ns:true (), F.eqf, a,[b]) }
    let mkNil ~loc = { it = Const(Scope.mkGlobal ~escape_ns:true (),F.nilf); loc }
    let mkCons ?loc a b =
      let loc = match loc with Some x -> x | None -> Loc.merge a.loc b.loc in
      { loc; it = App(Scope.mkGlobal ~escape_ns:true (),F.consf,a,[b]) }

    let list_to_lp_list ~loc l =
      let rec aux = function
        | [] -> mkNil ~loc
        | hd::tl ->
            let tl = aux tl in
            mkCons hd tl
        in
      aux l

    let ne_list_to_lp_list l =
      match List.rev l with
      | [] -> anomaly "Ast.list_to_lp_list on empty list"
      | h :: _ -> list_to_lp_list ~loc:h.loc l
      
    let rec lp_list_to_list = function
      | { it = App(Global { escape_ns = true }, c, x, [xs]) } when F.equal c F.consf  -> x :: lp_list_to_list xs
      | { it = Const(Global { escape_ns = true },c) } when F.equal c F.nilf -> []
      | { loc; it } -> error ~loc (Format.asprintf "%a is not a list" pp_t_ it)
    
  end

  type spill_info =
    | NoInfo (* before typing *)
    | Main of int (* how many arguments it stands for *)
    | Phantom of int (* phantom term used during type checking *)
  [@@ deriving show]
  type t_ =
   | Impl of bool * t * t (* `Impl(true,t1,t2)` ≡ `t1 => t2` and `Impl(false,t1,t2)` ≡ `t1 :- t2` *)
   | Const of Scope.t * F.t
   | Discard
   | Var of F.t * t list
   | App of Scope.t * F.t * t * t list
   | Lam of (F.t * Scope.language) option * ScopedTypeExpression.e option * TypeAssignment.t MutableOnce.t * t
   | CData of CData.t
   | Spill of t * spill_info ref
   | Cast of t * ScopedTypeExpression.e
   and t = { it : t_; loc : Loc.t; ty : TypeAssignment.t MutableOnce.t }
  [@@ deriving show]

  let type_of { ty } = assert(MutableOnce.is_set ty); TypeAssignment.deref ty

  open Format

  let lam = 0
  let app = 1

  let lvl_of = function
    | App _ -> app
    | Lam _ -> lam
    | _ -> 2

  let get_lam_name = function None -> F.from_string "_" | Some (n,_) -> n
  let mk_empty_lam_type name = MutableOnce.make (get_lam_name name)

  let build_infix_constant scope name loc : t = {loc; ty = MutableOnce.create (TypeAssignment.Val (Arr (Variadic, Prop, Prop))); it = Const (scope, name)}

  let is_infix_constant f =
    let infix = [F.andf; F.orf; F.eqf; F.isf; F.asf; F.consf] in
    List.mem f infix

  let intersperse e : 'a -> t list = function
    | [] | [_] as a -> a
    | x::xs -> x :: e x.loc :: xs

  let rec pretty_lam fmt n ste (mta:TypeAssignment.t MutableOnce.t) it =
    fprintf fmt "%a" F.pp (get_lam_name n);
    if MutableOnce.is_set mta then
      fprintf fmt ": %a " TypeAssignment.pretty (match MutableOnce.get mta with Val a -> a)
    else Option.iter (fun e -> fprintf fmt ": %a " ScopedTypeExpression.pretty_e e) ste;
    fprintf fmt "\\ %a" pretty it;

  and pretty fmt { it } = pretty_ fmt it
  and pretty_ fmt = function
    | Impl(true,t1,t2) -> fprintf fmt "(%a => %a)" pretty t1 pretty t2
    | Impl(_,t1,t2) -> fprintf fmt "(%a :- %a)" pretty t1 pretty t2
    | Const(_,f) -> fprintf fmt "%a" F.pp f
    | Discard -> fprintf fmt "_"
    | Lam(n, ste, mta, it) -> pretty_lam fmt n ste mta it
    | App(Global _,f,x,[]) when F.equal F.spillf f -> fprintf fmt "{%a}" pretty x
    | App(_,f,x,xs) when F.equal F.pif f || F.equal F.sigmaf f -> fprintf fmt "%a %a" F.pp f (Util.pplist ~pplastelem:(pretty_parens_lam ~lvl:app)  (pretty_parens ~lvl:app) " ") (x::xs)
    | App((Global _ as g),f,x,xs) when is_infix_constant f -> fprintf fmt "%a" (Util.pplist (pretty_parens ~lvl:0) " ") (intersperse (build_infix_constant g f) (x::xs))
    | App(_,f,x,xs) -> fprintf fmt "%a %a" F.pp f (Util.pplist (pretty_parens ~lvl:app) " ") (x::xs)
    | Var(f,[]) -> fprintf fmt "%a" F.pp f
    | Var(f,xs) -> fprintf fmt "%a %a" F.pp f (Util.pplist (pretty_parens ~lvl:app) " ") xs
    | CData c -> fprintf fmt "%a" CData.pp c
    | Spill (t,{ contents = NoInfo }) -> fprintf fmt "{%a}" pretty t
    | Spill (t,{ contents = Main _ }) -> fprintf fmt "{%a}" pretty t
    | Spill (t,{ contents = Phantom n}) -> fprintf fmt "{%a}/*%d*/" pretty t n
    | Cast (t,ty) -> fprintf fmt "(%a : %a)" pretty t ScopedTypeExpression.pretty_e ty (* TODO pretty *)
  and pretty_parens ~lvl fmt { it } =
    if lvl >= lvl_of it then fprintf fmt "(%a)" pretty_ it
    else pretty_ fmt it
  and pretty_parens_lam ~lvl fmt x =
    match x.it with Lam _ -> fprintf fmt "%a" pretty_ x.it | _ -> pretty_parens ~lvl fmt x
  

  let equal ?(types=true) t1 t2 =
    let rec eq ctx t1 t2 =
      match t1.it, t2.it with
      | Const(Global _ as b1,c1), Const(Global _ as b2,c2) -> b1 = b2 && F.equal c1 c2
      | Const(Bound l1,c1), Const(Bound l2,c2) -> l1 = l2 && eq_var ctx l1 c1 c2
      | Discard, Discard -> true
      | Var(n1,l1), Var(n2,l2) -> eq_uvar ctx n1 n2 && Util.for_all2 (eq ctx) l1 l2
      | App(Global _ as b1,c1,x,xs), App(Global _ as b2,c2,y,ys) -> b1 = b2 && F.equal c1 c2 && eq ctx x y && Util.for_all2 (eq ctx) xs ys
      | App(Bound l1,c1,x,xs), App(Bound l2,c2,y,ys) -> l1 = l2 && eq_var ctx l1 c1 c2 && eq ctx x y && Util.for_all2 (eq ctx) xs ys
      | Lam(None,ty1, _,b1), Lam (None,ty2,_, b2) -> eq ctx b1 b2 && (not types || Option.equal (ScopedTypeExpression.eqt (empty ())) ty1 ty2)
      | Lam(Some (c1,l1),ty1,_,b1), Lam(Some (c2,l2),ty2,_, b2) -> l1 = l2 && eq (push_ctx l1 c1 c2 ctx) b1 b2 && (not types || Option.equal (ScopedTypeExpression.eqt (empty ())) ty1 ty2)
      | Spill(b1,n1), Spill (b2,n2) -> n1 == n2 && eq ctx b1 b2
      | CData c1, CData c2 -> CData.equal c1 c2
      | Cast(t1,ty1), Cast(t2,ty2) -> eq ctx t1 t2 && (not types || ScopedTypeExpression.eqt (empty ()) ty1 ty2)
      | Impl(b1,s1,t1), Impl(b2,s2,t2) -> b1 = b2 && eq ctx t1 t2 && eq ctx s1 s2
      | _ -> false
    in
      eq (empty ()) t1 t2

    let compare _ _ = assert false

    let in_scoped_term, out_scoped_term, is_scoped_term =
    let open CData in
    let { cin; cout; isc } = declare {
        data_name = "hidden_scoped_term";
        data_pp = pretty;
        data_compare = (fun _ _ -> assert false);
        data_hash = Hashtbl.hash;
        data_hconsed = false;
      } in
    cin, cout, isc

  let rec of_simple_term ~loc = function
    | SimpleTerm.Discard -> Discard
    | Impl(b,t1,t2) -> Impl(b,of_simple_term_loc t1, of_simple_term_loc t2)
    | Const(s,c) -> Const(s,c)
    | Opaque c -> CData c
    | Cast(t,ty) -> Cast(of_simple_term_loc t, ScopedTypeExpression.of_simple_type_loc ty)
    | Lam(c,ty,t) -> Lam(c,Option.map ScopedTypeExpression.of_simple_type_loc ty, mk_empty_lam_type c,of_simple_term_loc t)
    | App(s,c,x,xs) when F.equal c F.implf || F.equal c F.implf -> 
      begin match xs with
        | [y] -> Impl(F.equal c F.implf,of_simple_term_loc x, of_simple_term_loc y)
        | _ -> error ~loc "Use of App for Impl is allowed, but the length of the list in 3rd position must be 1"
      end
    | App(s,c,x,xs) -> App(s,c,of_simple_term_loc x, List.map of_simple_term_loc xs)
    | Var(c,xs) -> Var(c,List.map of_simple_term_loc xs)
  and of_simple_term_loc { SimpleTerm.it; loc } =
    match it with
    | Opaque c when is_scoped_term c -> out_scoped_term c
    | _ -> { it = of_simple_term ~loc it; loc; ty = MutableOnce.make (F.from_string "Ty") }

    let unlock { it } = it

    (* naive, but only used by macros *)
    let fresh = ref 0
    let fresh () = incr fresh; F.from_string (Format.asprintf "%%bound%d" !fresh)

    let rec rename l c d t =
      match t with
      | Impl(b,t1,t2) -> Impl(b,rename_loc l c d t1, rename_loc l c d t2)
      | Const(Bound l',c') when l = l' && F.equal c c' -> Const(Bound l,d)
      | Const _ -> t
      | App(Bound l',c',x,xs) when l = l' && F.equal c c' ->
          App(Bound l,d,rename_loc l c d x, List.map (rename_loc l c d) xs)
      | App(g,v,x,xs) -> App(g,v,rename_loc l c d x, List.map (rename_loc l c d) xs)
      | Lam(Some (c',l'),_,_,_) when l = l' && F.equal c c' -> t
      | Lam(v,ty,tya,t) -> Lam(v,ty,tya,rename_loc l c d t)
      | Spill(t,i) -> Spill(rename_loc l c d t,i)
      | Cast(t,ty) -> Cast(rename_loc l c d t,ty)
      | Var(v,xs) -> Var(v,List.map (rename_loc l c d) xs)
      | Discard | CData _ -> t
    and rename_loc l c d { it; ty; loc } = { it = rename l c d it; ty; loc } 

    let beta t args =
      let rec fv acc { it } =
        match it with
        | Const(Bound l,c) -> Scope.Set.add (c,l) acc
        | Impl(_,a,b) -> List.fold_left fv acc [a;b]
        | Var (_,args) -> List.fold_left fv acc args
        | App(Bound l,c,x,xs) -> List.fold_left fv (Scope.Set.add (c,l) acc) (x::xs)
        | App(Global _,_,x,xs) -> List.fold_left fv acc (x::xs)
        | Lam(None,_,_,t) -> fv acc t
        | Lam(Some (c,l),_,_,t) -> Scope.Set.union acc @@ Scope.Set.remove (c,l) (fv Scope.Set.empty t)
        | Spill(t,_) -> fv acc t
        | Cast(t,_) -> fv acc t
        | Discard | Const _ | CData _ -> acc in
      let rec load_subst ~loc t (args : t list) map fvset =
        match t, args with
        | Lam(None,_,_,t), _ :: xs -> load_subst_loc t xs map fvset
        | Lam(Some c,_,_,t), x :: xs -> load_subst_loc t xs (Scope.Map.add c x map) (fv fvset x)
        | t, xs -> app ~loc (subst map fvset t) xs
      and load_subst_loc { it; loc } args map fvset =
        load_subst ~loc it args map fvset
      and subst (map : t Scope.Map.t) fv t =
        match t with
        | Impl(b,t1,t2) -> Impl(b,subst_loc map fv t1, subst_loc map fv t2)
        | Lam(None,ty,tya,t) -> Lam(None,ty,tya,subst_loc map fv t)
        | Lam(Some (c,l),ty,tya,t) when not @@ Scope.Map.mem (c,l) map && not @@ Scope.Set.mem (c,l) fv ->
            Lam(Some (c,l),ty,tya,subst_loc map fv @@ t)
        | Lam(Some (c,l),ty,tya,t) ->
            let d = fresh () in
            Lam(Some (d,l),ty,tya,subst_loc map fv @@ rename_loc l c d t)
        | Const(Bound l,c) when Scope.Map.mem (c,l) map -> unlock @@ Scope.Map.find (c,l) map
        | Const _ -> t
        | App(Bound l,c,x,xs) when Scope.Map.mem (c,l) map ->
            let hd = Scope.Map.find (c,l) map in
            unlock @@ app_loc hd (List.map (subst_loc map fv) (x::xs))
        | App(g,c,x,xs) -> App(g,c,subst_loc map fv x, List.map (subst_loc map fv) xs)
        | Var(c,xs) -> Var(c,List.map (subst_loc map fv) xs)
        | Spill(t,i) -> Spill(subst_loc map fv t,i)
        | Cast(t,ty) -> Cast(subst_loc map fv t,ty)
        | Discard | CData _ -> t
      and subst_loc map fv { it; ty; loc } = { it = subst map fv it; ty; loc }
      and app_loc { it; loc; ty } args : t = { it = app ~loc it args; loc; ty }
      and app ~loc t (args : t list) =
        if args = [] then t else
        match t with
        | Const(g,c) -> App(g,c,List.hd args,List.tl args)
        | App(g,c,x,xs) -> App(g,c,x,xs @ args)
        | Var(c,xs) -> Var(c,xs @ args)
        | Impl(_,_,_) -> error ~loc "cannot apply impl"
        | CData _ -> error ~loc "cannot apply cdata"
        | Spill _ -> error ~loc "cannot apply spill"
        | Discard -> error ~loc "cannot apply discard"
        | Cast _ -> error ~loc "cannot apply cast"
        | Lam _ -> load_subst ~loc t args Scope.Map.empty Scope.Set.empty
      in
        load_subst_loc t args Scope.Map.empty Scope.Set.empty

  module QTerm = struct
    include SimpleTerm
    let apply_elpi_var_from_quotation ({ SimpleTerm.it; loc } as o) l =
      if l = [] then o
      else
        let l = List.map of_simple_term_loc l in
        match it with
        | SimpleTerm.Opaque o when is_scoped_term o ->
            begin match out_scoped_term o with
            | { it = Var(f,xs); loc = loc'; ty } -> { SimpleTerm.loc; it = SimpleTerm.Opaque (in_scoped_term @@ { it = Var(f,xs @ l); loc = loc'; ty }) }
            | { it = Const(Bound g,f); loc = loc'; ty } when g = elpi_language ->
                { SimpleTerm.loc; it = SimpleTerm.Opaque (in_scoped_term @@ { it = App(Bound g,f,List.hd l, List.tl l); loc = loc'; ty }) }
            | x -> anomaly ~loc (Format.asprintf "The term is not an elpi varible coming from a quotation: @[%a@]" pretty x)
            end
        | x -> anomaly ~loc (Format.asprintf "The term is not term coming from a quotation: @[%a@]" pp_t_ x)
  
  
    let extend_spill_hyp_from_quotation { SimpleTerm.it; loc } hyps =
      match it with
      | SimpleTerm.Opaque o when is_scoped_term o ->
          begin match out_scoped_term o with
          | { it = Spill(t,i); loc } ->
            let impl = { loc; it = Impl(true, list_to_lp_list ~loc hyps, { loc; it = Opaque (in_scoped_term t) }) } in
            { loc; it = Opaque(in_scoped_term @@ { it = Spill(of_simple_term_loc impl,i); loc; ty = MutableOnce.make (F.from_string "Ty") })}
          | _ ->
            anomaly ~loc (Format.asprintf "The term is not a spill coming from a quotation: @[%a@]" pp_t_ it)
          end
      | x ->
         anomaly ~loc (Format.asprintf "The term is not coming from a quotation: @[%a@]" pp_t_ x)

    let is_spill_from_quotation { SimpleTerm.it } =
      match it with
      | SimpleTerm.Opaque o when is_scoped_term o ->
        begin match out_scoped_term o with
        | { it = Spill _ } -> true 
        | _ -> false
        end
      | _ -> false
  end

  let is_var = function Var _ -> true | _ -> false
end


module TypeList = struct

  type t = ScopedTypeExpression.t list
  [@@deriving show, ord]
  
  let make t = [t]
    
  let smart_map = smart_map
  
  let append x t = x :: List.filter (fun y -> not @@ ScopedTypeExpression.equal x y) t
  let merge t1 t2 = List.fold_left (fun acc x -> append x acc) (List.rev t1) t2

  let fold = List.fold_left
  
end

module State = Data.State

module QuotationHooks = struct
  
  type quotation = language:Scope.language -> State.t -> Ast.Loc.t -> string -> ScopedTerm.SimpleTerm.t
  
  type descriptor = {
    named_quotations : quotation StrMap.t;
    default_quotation : quotation option;
    singlequote_compilation : (string * quotation) option;
    backtick_compilation : (string * quotation) option;
  }
  
  let new_descriptor () = ref {
    named_quotations = StrMap.empty;
    default_quotation = None;
    singlequote_compilation = None;
    backtick_compilation = None;
  }
  
  let declare_singlequote_compilation ~descriptor name f =
    match !descriptor with
    | { singlequote_compilation = None } ->
        descriptor := { !descriptor with singlequote_compilation = Some(name,f) }; name
    | { singlequote_compilation = Some(oldname,_) } ->
          error("Only one custom compilation of 'ident' is supported. Current: "
            ^ oldname ^ ", new: " ^ name)
  let declare_backtick_compilation ~descriptor name f =
    match !descriptor with
    | { backtick_compilation = None } ->
        descriptor := { !descriptor with backtick_compilation = Some(name,f) }; name
    | { backtick_compilation = Some(oldname,_) } ->
          error("Only one custom compilation of `ident` is supported. Current: "
            ^ oldname ^ ", new: " ^ name)
  
  let set_default_quotation ~descriptor f =
    descriptor := { !descriptor with default_quotation = Some f }
  let register_named_quotation ~descriptor ~name:n f =
    descriptor := { !descriptor with named_quotations = StrMap.add n f !descriptor.named_quotations };
    n
  
end
  
module Arity = struct type t = int * Loc.t [@@deriving show, ord] end

exception CompileError of Loc.t option * string

let error ?loc msg = raise (CompileError(loc, msg))
