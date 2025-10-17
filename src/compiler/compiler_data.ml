open Elpi_util
open Elpi_parser
open Elpi_runtime
open Util
module F = Ast.Func

module Symbol = Data.Symbol

module ScopeContext = struct

  type language = string
  [@@ deriving show, ord]
  
  
  type ctx = { vmap : (language * F.t * F.t) list; uvmap : (F.t * F.t) list ref }
  let empty () = { vmap = []; uvmap = ref [] }
  
  let eq_var { vmap } language c1 c2 = List.mem (language,c1,c2) vmap
  let cmp_var ctx language c1 c2 =
    if eq_var ctx language c1 c2 then 0
    else
      let r = F.compare c1 c2 in
      if r = 0 then -1 else r
  
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
  
let elpi_language : ScopeContext.language = "lp"
let elpi_var : ScopeContext.language = "lp_var"
  
module MutableOnce : sig 
  type 'a t
  [@@ deriving show, ord]
  val make : F.t -> 'a t
  val create : 'a -> 'a t
  val set : ?loc:Loc.t -> 'a t -> 'a -> unit
  val unset : 'a t -> unit
  val get : 'a t -> 'a
  val get_name : 'a t -> F.t
  val is_set : 'a t -> bool
  val pretty : Format.formatter -> 'a t -> unit
end = struct
  type 'a t = F.t * 'a option ref
  [@@ deriving show, ord]

  let make f = f, ref None

  let create t = F.from_string "_", ref (Some t)

  let is_set (_,x) = Option.is_some !x
  let set ?loc (_,r) x =
    match !r with
    | None -> r := Some x
    | Some _ -> anomaly ?loc "MutableOnce"
  
  let get (_,x) = match !x with Some x -> x | None -> anomaly "get"
  let get_name (x,_) = x
  let unset (_,x) = x := None

  let pretty fmt (f,x) =
    match !x with
    | None -> Format.fprintf fmt "%a" F.pp f
    | Some _ -> anomaly "pp"
end

module TypeAssignment = struct

  type tmode = MRef of tmode MutableOnce.t | MVal of Mode.t
  [@@ deriving show]

  
  let rec deref_tmode = function
  | MRef r when MutableOnce.is_set r -> deref_tmode (MutableOnce.get r)
  | a -> a
  let compare_tmode m1 m2 =
    match deref_tmode m1, deref_tmode m2 with
    | MVal m1, MVal m2 -> Mode.compare m1 m2
    | _ -> anomaly "comparing an inferred mode declaration. Maybe some pred/func declaration is missing"

  let is_tmode_set t =
    match deref_tmode t with
    | MVal _ -> true
    | _ -> false

  let set_tmode m x =
    match deref_tmode m with
    | MVal _ -> assert false
    | MRef m -> MutableOnce.set m (MVal x)

  let rec pretty_tmode fmt = function
    | MRef x when MutableOnce.is_set x -> pretty_tmode fmt (MutableOnce.get x)
    | MRef x -> Format.fprintf fmt "?"
    | MVal m -> Mode.pretty fmt m

  let rec is_input = function
    | MRef x when MutableOnce.is_set x -> is_input (MutableOnce.get x)
    | MRef x -> false
    | MVal Mode.Input -> true
    | MVal Mode.Output -> false


  type 'a overloaded =
    | Single of 'a
    | Overloaded of 'a list
  [@@ deriving show, fold, iter]

  type ('uvar,'mode) t__ =
    | Prop of Ast.Structured.functionality
    | Any
    | Cons of F.t
    | App of F.t * ('uvar,'mode) t__ * ('uvar,'mode) t__ list
    | Arr of 'mode * Ast.Structured.variadic * ('uvar,'mode) t__ * ('uvar,'mode) t__
    | UVar of 'uvar
  [@@ deriving show, fold, ord]

  type 'a t_ = ('a,tmode) t__
  [@@ deriving show, fold]

  exception InvalidMode

  let cmp_aux cmp1 k =
    if cmp1 = 0 then k () else cmp1


  let (&&&) x y =
    if x = 0 then y else x

  let rec compare_t_ ~cmp_mode ~cmp_func c t1 t2 = match t1, t2 with
    | Prop d1, Prop d2 -> cmp_func d1 d2
    | Any, Any -> 0
    | Cons f1, Cons f2 -> F.compare f1 f2
    | App (f1,hd,tl), App (f2,hd1,tl1) -> 
      cmp_aux 
        (F.compare f1 f2)
        (fun () -> List.compare (compare_t_ ~cmp_mode ~cmp_func c) (hd::tl) (hd1::tl1))

    | Arr (m1, v1, l1, r1), Arr (m2, v2, l2, r2) ->
      (cmp_mode m1 m2) &&&
      cmp_aux
        (Ast.Structured.compare_variadic v1 v2) (fun () -> 
          cmp_aux (compare_t_ ~cmp_mode ~cmp_func c l1 l2) (fun () -> 
            compare_t_ ~cmp_mode ~cmp_func c r1 r2))
    | UVar v1, UVar v2 -> c v1 v2
    | Prop _, _ -> -1 | _, Prop _ -> 1
    | Any   , _ -> -1 | _, Any    -> 1
    | Cons _, _ -> -1 | _, Cons _ -> 1
    | App _ , _ -> -1 | _, App _  -> 1
    | Arr _ , _ -> -1 | _, Arr _  -> 1

  type skema = Lam of F.t * skema | Ty of F.t t_
  [@@ deriving show]

  type type_abbrevs = (skema * Ast.Loc.t) F.Map.t
  [@@deriving show]

  let compare_skema ~cmp_mode ~cmp_func sk1 sk2 =
    let rec aux ctx sk1 sk2 =
      match sk1, sk2 with
      | Lam (f1,sk1), Lam(f2,sk2) -> aux (ScopeContext.push_ctx elpi_language f1 f2 ctx) sk1 sk2
      | Ty t1, Ty t2 -> compare_t_ ~cmp_mode ~cmp_func (ScopeContext.cmp_var ctx elpi_language) t1 t2
      | Lam _, Ty _ -> -1
      | Ty _, Lam _ -> 1
    in
      aux (ScopeContext.empty ()) sk1 sk2

  type overloaded_symbol = Symbol.t overloaded
  [@@ deriving show]

  type t = Val of t MutableOnce.t t_
  [@@ deriving show]

  type ty = t MutableOnce.t t_
  [@@ deriving show]


  let create t = MutableOnce.create (Val t)

  let unval (Val x) = x

  let rec deref m =
    match unval @@ MutableOnce.get m with
    | UVar m when MutableOnce.is_set m -> deref m
    | x -> x

  let deref_opt m =
    if MutableOnce.is_set m then Some (deref m) else None

  open Format
  let pretty (f : formatter -> (formatter -> 'a t_ -> unit) -> 'a -> unit) fmt tm =

    let arrs = 0 in
    let app = 1 in

    let rec arrow_tail = function
      | Prop x -> Some x
      | Arr(_,_,_,x) -> arrow_tail x
      | _ -> None in

    let lvl_of = function
      | Arr _ -> arrs
      | App _ -> app
      | _ -> 2 in

    let show_mode fmt m = Format.fprintf fmt "%a" pretty_tmode m
    in

    let rec is_func_modes input = function
     | Arr(m,_,_,t) when is_input m && input -> is_func_modes input t
     | Arr(m,_,_,t) when not (is_input m) && input -> is_func_modes false t
     | Arr(m,_,_,t) when not (is_input m) && not input -> is_func_modes false t
     | Prop _ -> true
     | _ -> false
    in

    let rec pretty fmt = function
      | Prop Relation -> fprintf fmt "(pred)"
      | Prop Function -> fprintf fmt "(func)"
      | Any -> fprintf fmt "any"
      | Cons c -> F.pp fmt c
      | App(f,x,xs) -> fprintf fmt "@[<hov 2>%a@ %a@]" F.pp f (Util.pplist (pretty_parens ~lvl:app) " ") (x::xs)
      | Arr(m,NotVariadic,s,t) as x -> 
          begin match arrow_tail t with
            | None -> fprintf fmt "@[<hov 2>%a ->@ %a@]" (pretty_parens ~lvl:arrs) s pretty t
            | Some Ast.Structured.Function when is_func_modes true x -> fprintf fmt "@[<hov 2>(func%a)@]" (pretty_func ~fst:true true) x
            | Some _ -> fprintf fmt "@[<hov 2>(pred %a)@]" (pretty_pred_mode m) (s, t) 
          end
      | Arr(m,Variadic,s,t) -> fprintf fmt "variadic %a %a" (pretty_parens ~lvl:arrs) s pretty t
      | UVar m -> f fmt pretty m
      (* | UVar m -> MutableOnce.pretty fmt m *)
    and pretty_parens ~lvl fmt = function
      | UVar m -> f fmt (pretty_parens ~lvl) m
      | t when lvl >= lvl_of t -> fprintf fmt "(%a)" pretty t
      | t -> pretty fmt t
    and pretty_pred_mode m fmt (s, t) =
      fprintf fmt "@[<hov 2>%a:%a@]" show_mode m (pretty_parens ~lvl:arrs) s;
      match t with
      | Prop _ -> ()
      | Arr(m, v, s', r) -> fprintf fmt ", %s%a" (if v = Variadic then "variadic " else "") (pretty_pred_mode m) (s',r)
      | _ -> assert false
    and pretty_func ?(fst=false) input fmt x =
      match x with
      | Prop _ -> ()
      | Arr(m, v, s, r) ->
        let input =
          if not (is_input m) && input then begin fprintf fmt "@ ->"; false end
          else (if not fst then fprintf fmt ","; input) in
        fprintf fmt "@[<hov 2>@ %a%a@]" (pretty_parens ~lvl:arrs) s (pretty_func input) r
      | _ -> assert false
    in
    let pretty fmt t = Format.fprintf fmt "@[%a@]" pretty t
  in 
  pretty fmt tm

  let pretty_mut_once = 
    pretty (fun fmt f t -> if MutableOnce.is_set t then f fmt (deref t) else MutableOnce.pretty fmt t)

  let pretty_ft fmt t =
    pretty (fun fmt _ (t:F.t) -> F.pp fmt t) fmt t

  let pretty_skema fmt sk =
    let rec aux = function
      | Lam (_,t) -> aux t
      | Ty t -> pretty_ft fmt t in
    aux sk

  let pretty_skema = pretty_skema

  let pretty_skema_w_id fmt (_,sk) = pretty_skema fmt sk

  let pretty_overloaded_skema fmt = function
    | Single t -> pretty_skema_w_id fmt t
    | Overloaded l -> pplist pretty_skema_w_id "," fmt l

  let set m v = MutableOnce.set m (Val v)

  let new_ty () : t MutableOnce.t = MutableOnce.make (F.from_string "Ty")
  let mkProp f : t MutableOnce.t =
    let r = MutableOnce.make (F.from_string "Ty") in
    set r (Prop f);
    r

  let mkList x : t MutableOnce.t =
    let r = MutableOnce.make (F.from_string "Ty") in
    set r (App(F.from_string "list",x,[]));
    r


  let nparams (t : skema) =
      let rec aux = function Ty _ -> 0 | Lam(_,t) -> 1 + aux t in
      aux t
  
  let rec subst map = function
    | (Prop _ | Any | Cons _) as x -> x
    | App(c,x,xs) -> App (c,subst map x,List.map (subst map) xs)
    | Arr(m,v,s,t) -> Arr(m,v,subst map s, subst map t)
    | UVar c ->
        match map c with
        | Some x -> x
        | None -> anomaly "TypeAssignment.subst"

  let fresh (sk: skema) =
    let rec fresh map = function
      | Lam(c,t) -> fresh (F.Map.add c (UVar (MutableOnce.make c)) map) t
      | Ty t -> if F.Map.is_empty map then (Obj.magic t), map else (subst (fun x -> F.Map.find_opt x map) t), map
  in
    fresh F.Map.empty sk

  let map_overloaded f = function
    | Single sk -> Single (f sk)
    | Overloaded l -> Overloaded (List.map f l)

  let fresh_overloaded o = map_overloaded (fun x -> fst @@ fresh x) o

  let rec apply m sk args =
    match sk, args with
    | Ty t, [] -> if F.Map.is_empty m then Obj.magic t else subst (fun x -> F.Map.find_opt x m) t
    | Lam(c,t), x::xs -> apply (F.Map.add c x m) t xs
    | _ -> assert false (* kind checker *)

  let apply (sk:skema) args = apply F.Map.empty sk args


  let rec is_prop ~type_abbrevs = function
    | Prop f -> Some f
    | Cons a when F.Map.mem a type_abbrevs -> let ty = apply (fst @@ F.Map.find a type_abbrevs) [] in is_prop ~type_abbrevs ty
    | App (a,x,xs) when F.Map.mem a type_abbrevs -> let ty = apply (fst @@ F.Map.find a type_abbrevs) (x::xs) in is_prop ~type_abbrevs ty
    | Any | Cons _ | App _ | UVar _ -> None
    | Arr(_,_,_,t) -> is_prop ~type_abbrevs t


  let eq_skema_w_id n (symb1,x) (symb2,y) = 
    try compare_skema ~cmp_mode:compare_tmode ~cmp_func:Ast.Structured.compare_functionality x y = 0
    with InvalidMode -> 
      error ~loc:(Symbol.get_loc symb1) 
        (Format.asprintf "@[<v>duplicate mode declaration for %a.@ - %a %a@ - %a %a@]" F.pp n Symbol.pp symb1 pretty_skema x Symbol.pp symb2 pretty_skema y)



  let check_same_mode ~loc1 ~loc2 (s1, x) (s2, y) =
    if compare_skema ~cmp_mode:compare_tmode ~cmp_func:Ast.Structured.compare_functionality x y <> 0 then
      error ~loc:loc2 (Format.asprintf "@[<v>Two types for the symbol %s cannot only differ on modes or functionality.@\n@[<hov 2>Current declaration:@;<2 0>%a@]@\n@[<v 2>Previous declaration: %a@ (%s)@]@]" (Symbol.pretty s1) pretty_skema x pretty_skema y (Loc.show loc1))

  let undup_skemas sk_of_s osl =
    let l = osl |> List.map (fun x -> x, sk_of_s x) in
    let filtered = ref [] in
    let eq_skema ((s1,x) as l) ((s2,y) as r) = 
      let b = compare_skema ~cmp_mode:(fun _ _ -> 0) ~cmp_func:(fun _ _ -> 0) x y = 0 in
      if b then check_same_mode ~loc1:(Symbol.get_loc s1) ~loc2:(Symbol.get_loc s2) l r;
      if b then filtered := (s1,s2) :: !filtered;
      b in      
    let l =
      let rec undup = function
        | [] -> []
        | (s, _ as x) :: xs when List.exists (eq_skema x) xs -> undup xs
        | x :: xs -> x :: undup xs in
      undup l in
    match List.map fst l with
    | [] -> assert false
    | [x] -> !filtered, Single x
    | l -> !filtered, Overloaded l

  let merge_skema sk1 sk2 =
    if compare_skema ~cmp_mode:compare_tmode ~cmp_func:Ast.Structured.compare_functionality sk1 sk2 <> 0 then anomaly "merging different skemas";
    sk1

  let compare_t_ a b = compare_t_ ~cmp_mode:compare_tmode ~cmp_func:Ast.Structured.compare_functionality a b
  let compare_skema a b = compare_skema ~cmp_mode:compare_tmode ~cmp_func:Ast.Structured.compare_functionality a b

  exception Not_monomorphic
  let is_monomorphic (Val t) =
    let rec map = function
      | UVar r when MutableOnce.is_set r -> map (deref r)
      | UVar _ -> raise Not_monomorphic
      | (Prop _ | Any | Cons _) as v -> v
      | App(c,x,xs) -> App(c,map x, List.map map xs)
      | Arr(m,b,s,t) -> Arr(m,b,map s,map t)
    in
    try 
      let t = map t in
      Some (Ty (Obj.magic t : F.t t_)) (* No UVar nodes *)
    with Not_monomorphic -> None

  let vars_of (Val t)  =
    fold_t__
      (fun (xs,acc) (x : t MutableOnce.t) -> if MutableOnce.is_set x then xs, acc else x :: xs, acc)
      (fun (acc,xs) (x : tmode) ->
         match x with
         | MRef x when MutableOnce.is_set x -> acc,xs
         | MRef x -> acc,x :: xs
         | MVal _ -> acc,xs)
      ([],[]) t

  let to_func_mode ~(type_abbrevs:type_abbrevs) f = 
    let apply_ta f c acc l =
      match F.Map.find_opt c type_abbrevs with
      | None -> None
      | Some (e,_) -> f acc (apply e l)
    in
    let rec aux acc = function
    | Prop f -> Some (Some f, List.rev acc)
    | Any | UVar _ -> None
    | Cons c -> apply_ta aux c acc []
    | App (c, x, xs) -> apply_ta aux c acc (x::xs)
    | Arr (mode, _, l, r) ->
        let m = match deref_tmode mode with
          | MVal v -> v
          | MRef _ -> Output 
        in
        match aux [] l with
        | None -> aux (Mode.Fo m :: acc) r
        | Some (_,e) -> aux (Mode.Ho (m, e) :: acc) r
    in
    match aux [] f with None -> (None, []) | Some e -> e

  let rec skema_to_func_mode ~(type_abbrevs:type_abbrevs) = function
    | Lam (_,x) -> skema_to_func_mode ~type_abbrevs x
    | Ty t ->  to_func_mode ~type_abbrevs t

end

module TypingEnv : sig

  type indexing =
  | Index of Elpi_runtime.Data.pred_info
  | DontIndex
  [@@deriving show]

  type symbol_metadata = {
    ty : TypeAssignment.skema;
    indexing : indexing;
    availability : Elpi_parser.Ast.Structured.symbol_availability;
    implemented_in_ocaml : bool;
  }
  [@@deriving show]

  val compatible_indexing : indexing -> indexing -> bool

  type t = {
    symbols : symbol_metadata Symbol.QMap.t;
    overloading : Symbol.t TypeAssignment.overloaded F.Map.t;
  }
  [@@deriving show]

  val empty : t

  val resolve_name : F.t -> t -> Symbol.t TypeAssignment.overloaded
  val resolve_symbol : Symbol.t -> t -> symbol_metadata
  val resolve_symbol_opt : Symbol.t -> t -> symbol_metadata option
  val merge_envs : t -> t -> t

  val iter_names : (F.t -> Symbol.t TypeAssignment.overloaded -> unit) -> t -> unit
  val iter_symbols : (Symbol.t -> symbol_metadata -> unit) -> t -> unit

  val same_symbol : t -> Symbol.t -> Symbol.t -> bool
  val compare_symbol : t -> Symbol.t -> Symbol.t -> int

  val undup : t -> Symbol.t list -> Symbol.t list
  val all_symbols : t -> (Symbol.t * symbol_metadata) list
  val mem_symbol : t -> Symbol.t -> bool
  val canon : t -> Symbol.t -> Symbol.t

  val set_as_implemented_in_ocaml : t -> Symbol.t -> t

end = struct

  type indexing =
    | Index of Elpi_runtime.Data.pred_info
    | DontIndex
  [@@deriving show]

  type symbol_metadata = {
    ty : TypeAssignment.skema;
    indexing : indexing;
    availability : Elpi_parser.Ast.Structured.symbol_availability;
    implemented_in_ocaml : bool;
  }
  [@@deriving show]

  type t = {
    symbols : symbol_metadata Symbol.QMap.t;
    overloading : Symbol.t TypeAssignment.overloaded F.Map.t;
  }
  [@@deriving show]

  let set_as_implemented_in_ocaml e s =
    match Symbol.QMap.find_opt s e.symbols with
    | None -> assert false
    | Some m -> { e with symbols = Symbol.QMap.add s { m with implemented_in_ocaml = true } e.symbols }

  let compatible_indexing i1 i2 =
    match i1, i2 with
    | Index { indexing = i1; mode = m1 }, Index { indexing = i2; mode = m2 } ->
        Elpi_runtime.Data.compare_indexing i1 i2 == 0 && Elpi_util.Util.Mode.compare_hos m1 m2 == 0
    | DontIndex, _ -> true
    | _, DontIndex -> true
  
  let empty = {symbols = Symbol.QMap.empty; overloading = F.Map.empty}
  
  let canon symbols s = Symbol.UF.find (Symbol.QMap.get_uf symbols) s
  
  let resolve_name f { overloading; symbols } : Symbol.t TypeAssignment.overloaded =
    match F.Map.find f overloading with
    | Single s -> Single (canon symbols s)
    | Overloaded l -> Overloaded (List.map (canon symbols) l)
  
  let resolve_symbol s { symbols } = Symbol.QMap.find s symbols
  let resolve_symbol_opt s { symbols } = Symbol.QMap.find_opt s symbols
  
  
  let merge_indexing s idx1 idx2 =
    if not @@ compatible_indexing idx1 idx2 then
      error ~loc:(Symbol.get_loc s) ("Incompatible indexing options for symbol " ^ Symbol.get_str s);
    idx1
  
  let merge_availability s a1 a2 =
    let open Ast.Structured in
    match a1, a2 with
    | Elpi, Elpi -> Elpi
    | OCaml (p1), OCaml (p2) when Symbol.compare_provenance p1 p2 = 0 -> a1
    | OCaml ((Builtin _|Core)), OCaml ((File _)) -> a1
    | OCaml ((File _)), OCaml ((Builtin _|Core)) -> a2
    | _ ->
       error ~loc:(Symbol.get_loc s) ("Incompatible provenance for symbol " ^ Symbol.get_str s ^ ": " ^  show_symbol_availability a1 ^ " != " ^ show_symbol_availability a2)
  
  
  let merge_symbol_metadata s
      { ty = ty1; indexing = idx1; availability = a1; implemented_in_ocaml = o1; }
       { ty = ty2; indexing = idx2; availability = a2; implemented_in_ocaml = o2; } =
    { ty = TypeAssignment.merge_skema ty1 ty2;
      indexing = merge_indexing s idx1 idx2;
      availability = merge_availability s a1 a2;
      implemented_in_ocaml = o1 || o2;
    }
  
  let o2l = function  TypeAssignment.Single x -> [x] | Overloaded l -> l

  let merge_envs   { symbols = s1; overloading = o1 } { symbols = s2; overloading = o2 } =
    let symbols = Symbol.QMap.union merge_symbol_metadata s1 s2 in
    let to_unite = ref [] in
    let overloading = F.Map.union (fun f l1 l2 ->
      (* We give precedence to recent type declarations over old ones *)
      let to_u, l = TypeAssignment.undup_skemas (fun x -> (Symbol.QMap.find x symbols).ty) (o2l l1 @ o2l l2) in
      to_unite := to_u :: !to_unite;
      Some l
      ) o1 o2 in
    let to_unite = List.concat !to_unite in
    let symbols =
      List.fold_right (fun (x,y) -> Symbol.QMap.unify merge_symbol_metadata x y) to_unite symbols in
    { overloading; symbols }
  
  let iter_names f { overloading } = F.Map.iter f overloading
  let iter_symbols f { symbols } = Symbol.QMap.iter f symbols
  let same_symbol { symbols } x y =
    let uf = Symbol.QMap.get_uf symbols in
    Symbol.equal ~uf x y

  let compare_symbol { symbols } x y =
    let uf = Symbol.QMap.get_uf symbols in
    Symbol.compare ~uf x y
  
  let undup { symbols } l =
    let uf = Symbol.QMap.get_uf symbols in
    Symbol.undup ~uf l
  
  let all_symbols { symbols } = Symbol.QMap.bindings symbols
  let mem_symbol  { symbols } x = Symbol.QMap.mem x symbols
  
  let canon { symbols } x = canon symbols x

end
module SymbolResolver : sig
  type resolution
  [@@deriving show]

  val compare : TypingEnv.t -> resolution -> resolution -> int
  val clone : resolution -> resolution

  val make : unit -> resolution
  val resolve : TypingEnv.t -> resolution -> Symbol.t -> unit
  val resolved_to : TypingEnv.t -> resolution -> Symbol.t option
  val is_resolved_to : TypingEnv.t -> resolution -> Symbol.t -> bool
  val is_resolved_to_builtin : TypingEnv.t -> resolution -> bool

end = struct

  type resolution = Symbol.t option ref
  [@@deriving show]

  let clone r =
    match !r with
    | None -> ref None
    | Some x -> ref (Some x)

  let compare env r1 r2 =
    match !r1, !r2 with
    | Some s1, Some s2 -> TypingEnv.compare_symbol env s1 s2
    | Some _, None -> -1
    | None, Some _ -> 1
    | _ -> 0

  let make () = ref None
  let resolve env r s =
    match !r with
    | None -> r := Some s
    | Some s' ->
        if not @@ TypingEnv.same_symbol env s' s then
          anomaly ("SymbolResolver: new " ^ Symbol.show s ^ " != old " ^ Symbol.show s');
        r := Some s

  let resolved_to env r =
    match !r with
    | None -> None
    | Some x -> Some (TypingEnv.canon env x)

  let is_resolved_to env r s =
    match resolved_to env r with
    | None -> false
    | Some s1 -> TypingEnv.same_symbol env s s1

  let is_resolved_to_builtin env r =
    match resolved_to env r with
    | None -> false
    | Some r ->
        match TypingEnv.resolve_symbol_opt r env with
        | None -> false
        | Some s -> s.implemented_in_ocaml

end


module Scope = struct

  type language = ScopeContext.language
  [@@ deriving show, ord]

  type t =
    | Bound  of language (* bound by a lambda, stays bound *)
    | Global of {
        escape_ns : bool; (* when true name space elimination does not touch this constant *)
        resolved_to : SymbolResolver.resolution;
      }
  [@@ deriving show]

  (* The compare function ignores the resolved_to field *)
  let compare env t1 t2 = match t1, t2 with
    | Bound b1, Bound b2 -> String.compare b1 b2
    | Global g1, Global g2 -> 
        let v = SymbolResolver.compare env g1.resolved_to g2.resolved_to in
        if v = 0 then Bool.compare g1.escape_ns g2.escape_ns
        else v
    | Bound _, Global _ -> 1
    | Global _, Bound _ -> -1

  let equal env x y = compare env x y = 0

  let clone = function Bound _ as t -> t | Global {escape_ns; resolved_to} -> Global {escape_ns; resolved_to = SymbolResolver.clone resolved_to}

  module Map = Map.Make(struct
    type t = F.t * language
    [@@ deriving show, ord]
  end)
  module Set = Set.Make(struct
    type t = F.t * language
    [@@ deriving show, ord]
  end)

  let mkGlobal ?(escape_ns=false) () =
    Global { escape_ns ; resolved_to = SymbolResolver.make () }
    
  let mkResolvedGlobal types symb =
    let resolved_to = SymbolResolver.make () in
    SymbolResolver.resolve types resolved_to symb;
    Global { escape_ns = true ; resolved_to }

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
    | Prop of Ast.Structured.functionality
    | Const of Scope.t * F.t
    | App of Scope.t * F.t * e * e list
    | Arrow of Mode.t * Ast.Structured.variadic * e * e
  and e = { it : t_; loc : Loc.t }
  [@@ deriving show]


  open Format

  let arrs = 0
  let app = 1

  let lvl_of = function
    | Arrow _ -> arrs
    | App _ -> app
    | _ -> 2

  let rec is_prop = function
    | Prop f -> Some f
    | Any | Const _ | App _ -> None
    | Arrow(_,_,_,t) -> is_prop t.it

  let rec pretty_e fmt = function
    | Any -> fprintf fmt "any"
    | Const(_,c) -> F.pp fmt c
    | Prop _ -> fprintf fmt "prop"
    | App(_, f,x,xs) -> fprintf fmt "@[<hov 2>%a@ %a@]" F.pp f (Util.pplist (pretty_e_parens ~lvl:app) " ") (x::xs)
    | Arrow(m,v,s,t) as p -> 
      (match is_prop p with
      | None -> fprintf fmt "@[<hov 2>%a ->@ %a@]" (pretty_e_parens ~lvl:arrs) s pretty_e_loc t
      | Some Function -> fprintf fmt "@[<hov 2>func%a@]" (pretty_prop m v s t) ()
      | Some Relation -> fprintf fmt "@[<hov 2>pred%a@]" (pretty_prop m v s t) ()
      )

  and pretty_prop m v l r fmt () =
    let show_var = function Ast.Structured.Variadic -> ".." | _ -> "" in
    match r.it with
    | Prop _ -> fprintf fmt "."
    | _  -> fprintf fmt "%a %s->@ %a" (*Mode.pretty m*) pretty_e_loc l (show_var v) pretty_e_loc r
  and pretty_e_parens ~lvl fmt = function
    | t when lvl >= lvl_of t.it -> fprintf fmt "(%a)" pretty_e_loc t
    | t -> pretty_e_loc fmt t
  and pretty_e_loc fmt { it } = pretty_e fmt it
  let pretty_e fmt (t : e) = Format.fprintf fmt "@[%a@]" pretty_e_loc t


  let rec of_simple_type = function
    | SimpleType.Any -> Any
    | Con c -> Const(Scope.mkGlobal (),c)
    | App(c,x,xs) -> App(Scope.mkGlobal (),c,of_simple_type_loc x,List.map of_simple_type_loc xs)
    | Arr(s,t) -> Arrow(Output, NotVariadic,of_simple_type_loc s, of_simple_type_loc t)
  and of_simple_type_loc { it; loc } = { it = of_simple_type it; loc }

  type v_ =
    | Lam of F.t * v_
    | Ty of e
  [@@ deriving show]

  type t = {
    name : F.t;
    value : v_;
    nparams : int;
    loc : Loc.t;
    index : Ast.Structured.predicate_indexing option;
    availability : Ast.Structured.symbol_availability;  
  }
  [@@ deriving show]

  let pretty fmt { value } =
    let rec pretty fmt = function
      | Lam(_,x) -> pretty fmt x
      | Ty e -> pretty_e fmt e in
    Format.fprintf fmt "@[%a@]" pretty value

  let rec eqt env ctx t1 t2 =
    match t1.it, t2.it with
    | Const(Global _ as b1,c1), Const(Global _ as b2,c2) -> Scope.compare env b1 b2 == 0 && F.equal c1 c2
    | Const(Bound l1,c1), Const(Bound l2,c2) -> Scope.compare_language l1 l2 == 0 && eq_var ctx l1 c1 c2
    | App(Global _, c1,x,xs), App(Global _, c2,y,ys) -> F.equal c1 c2 && eqt env ctx x y && Util.for_all2 (eqt env ctx) xs ys
    | App(Bound _,_,_,_), _ -> assert false
    | _, App(Bound _,_,_,_) -> assert false
    | Arrow(m1, b1,s1,t1), Arrow(m2, b2,s2,t2) -> Mode.compare m1 m2 == 0 && b1 = b2 && eqt env ctx s1 s2 && eqt env ctx t1 t2
    | Any, Any -> true
    | Prop f1, Prop f2 -> Ast.Structured.compare_functionality f1 f2 == 0
    | _ -> false

  let rec eq env ctx t1 t2 =
    match t1, t2 with
    | Lam(c1,b1), Lam(c2,b2) -> eq env (push_ctx "lp" c1 c2 ctx) b1 b2
    | Ty t1, Ty t2 -> eqt env ctx t1 t2
    | _ -> false

  let equal env { name = n1; value = x } { name = n2; value = y } = F.equal n1 n2 && eq env (empty ()) x y

  let compare _ _ = assert false

  let rec smart_map_scoped_loc_ty f ({ it; loc } as orig) =
    let it' = smart_map_scoped_ty f it in
    if it' == it then orig else { it = it'; loc }
  and smart_map_scoped_ty f orig =
    match orig with
    | Any | Prop _ -> orig
    | Const((Scope.Bound _| Scope.Global { escape_ns = true }),_) -> orig
    | Const(Scope.Global _ as g,c) ->
        let c' = f c in
        if c == c' then orig else Const(g,c')
    | App(Bound _,_,_,_) -> assert false
    | App(Global g as s, c,x,xs) ->
        let c' = if g.escape_ns then c else f c in
        let x' = smart_map_scoped_loc_ty f x in
        let xs' = smart_map (smart_map_scoped_loc_ty f) xs in
        if c' == c && x' == x && xs' == xs then orig else App(s,c',x',xs')
    | Arrow(m,v,x,y) ->
        let x' = smart_map_scoped_loc_ty f x in
        let y' = smart_map_scoped_loc_ty f y in
        if x' == x && y' == y then orig else Arrow(m,v,x',y')

  let rec smart_map_tye f = function
    | Lam(c,t) as orig ->
        let t' = smart_map_tye f t in
        if t == t' then orig else Lam(c,t')
    | Ty t as orig ->
      let t' = smart_map_scoped_loc_ty f t in
      if t == t' then orig else Ty t'

  let smart_map f ({ name; value; nparams; loc; index; availability } as orig) =
    let name' = f name in
    let value' = smart_map_tye f value in
    if name == name' && value' == value then orig
    else { name = name'; value = value'; nparams; loc; index; availability }

end

module ScopedTerm = struct
  open ScopeContext

  module SimpleTerm = struct

  type impl_kind = L2R | L2RBang | R2L
  [@@ deriving show]
  
  let is_implf f = let open Ast in Func.equal f Func.implf || Func.equal f Func.implbangf || Func.equal f Func.rimplf
  
  let func_to_impl_kind f =
    let open Ast in
    if Func.equal f Func.implf then L2R
    else if Func.equal f Func.implbangf then L2RBang
    else if Func.equal f Func.rimplf then R2L
    else anomaly ("not an implication " ^ F.show f)
    
  (* User Visible *)
    type t_ =
      | Impl of impl_kind * Loc.t * t * t (* `Impl(true,t1,t2)` ≡ `t1 => t2` and `Impl(false,t1,t2)` ≡ `t1 :- t2` *)
      | Const of Scope.t * F.t
      | Discard
      | Var of F.t * Loc.t * t list
      | App of Scope.t * F.t * Loc.t * t * t list
      | Lam of (F.t * Loc.t * Scope.language) option * ScopedTypeExpression.SimpleType.t option * t
      | Opaque of CData.t
      | Cast of t * ScopedTypeExpression.SimpleType.t
    and t = { it : t_; loc : Loc.t }
   [@@ deriving show]

   type constant = int
   let mkGlobal ~loc c = { loc; it = Const(Scope.mkGlobal ~escape_ns:true (),Data.Symbol.get_func @@ Constants.Map.find c Data.Global_symbols.table.c2s) }
   let mkBound ~loc ~language n = { loc; it = Const(Bound language,n)}
   let mkAppGlobal ~loc ~hdloc c x xs = { loc; it = App(Scope.mkGlobal ~escape_ns:true (),Data.Symbol.get_func @@ Constants.Map.find c Data.Global_symbols.table.c2s,hdloc,x,xs) }
   let mkAppBound ~loc ~hdloc ~language n x xs = { loc; it = App(Bound language,n,hdloc,x,xs) }
   let mkVar ~loc ~hdloc n l = { loc; it = Var(n,hdloc,l) }
   let mkOpaque ~loc o = { loc; it = Opaque o }
   let mkCast ~loc t ty = { loc; it = Cast(t,ty) }
   let mkDiscard ~loc = { loc; it = Discard }
   let mkLam ~loc n ?ty t =  { loc; it = Lam(n,ty,t)  }
   let mkImplication ~loc ~hdloc s t = { loc; it = Impl(L2R,hdloc,s,t) }
   let mkPi ~loc ~hdloc n ~nloc ?ty t = { loc; it = App(Scope.mkGlobal ~escape_ns:true (),F.pif,hdloc,{ loc; it = Lam (Some (n,nloc,elpi_language),ty,t) },[]) }
   let mkConj ~loc ~hdloc = function
     | [] -> { loc; it = Const(Scope.mkGlobal ~escape_ns:true (), F.truef) }
     | [x] -> x
     | x :: xs -> { loc; it = App(Scope.mkGlobal ~escape_ns:true (), F.andf, hdloc, x, xs)}
    let mkEq ~loc ~hdloc a b = { loc; it = App(Scope.mkGlobal ~escape_ns:true (), F.eqf, hdloc, a,[b]) }
    let mkNil ~loc = { it = Const(Scope.mkGlobal ~escape_ns:true (),F.nilf); loc }
    let mkCons ?loc ~hdloc a b =
      let loc = match loc with Some x -> x | None -> Loc.merge a.loc b.loc in
      { loc; it = App(Scope.mkGlobal ~escape_ns:true (),F.consf,hdloc,a,[b]) }

    let list_to_lp_list ~loc l =
      let rec aux = function
        | [] -> mkNil ~loc
        | hd::tl ->
            let tl = aux tl in
            mkCons ~hdloc:loc hd tl
        in
      aux l

    let ne_list_to_lp_list l =
      match List.rev l with
      | [] -> anomaly "Ast.list_to_lp_list on empty list"
      | h :: _ -> list_to_lp_list ~loc:h.loc l
      
    let rec lp_list_to_list = function
      | { it = App(Global { escape_ns = true }, c, _, x, [xs]) } when F.equal c F.consf  -> x :: lp_list_to_list xs
      | { it = Const(Global { escape_ns = true },c) } when F.equal c F.nilf -> []
      | { loc; it } -> error ~loc (Format.asprintf "%a is not a list" pp_t_ it)
    
  end

  type 'scope const = { scope: 'scope; name: F.t; ty: TypeAssignment.t MutableOnce.t; loc : Loc.t }
  [@@ deriving show]

  let mk_const ?(ty = MutableOnce.make F.dummyname) ~scope name ~loc : 'a const = { scope; name; ty; loc } 
  let mk_bound_const ?ty ~lang name ~loc = mk_const ?ty ~scope:(Scope.Bound lang) name ~loc

  let bind_const (n : string const) : Scope.t const = { n with scope = Scope.Bound n.scope }

  let mk_global_const ~name ~loc : 'a const = mk_const ~scope:(Scope.mkGlobal ()) name ~loc
  let const_of_symb ~types symb ~loc : 'a const = mk_const ~scope:(Scope.mkResolvedGlobal types symb) (Symbol.get_func symb) ~loc
  let clone_const ?(clone_scope = Fun.id) {scope;name; loc } = mk_const ~scope:(clone_scope scope) name ~loc

  type spill_info =
    | NoInfo (* before typing *)
    | Main of int (* how many arguments it stands for *)
    | Phantom of int (* phantom term used during type checking *)
  [@@ deriving show]

  type t_ =
   | Impl of SimpleTerm.impl_kind * Loc.t * t * t (* `Impl(true,t1,t2)` ≡ `t1 => t2` and `Impl(false,t1,t2)` ≡ `t1 :- t2` *)
   | Discard
   | Var of Scope.t const * t list
   | App of Scope.t const * t list
   | Lam of (Scope.language const) option * ScopedTypeExpression.e option * t

   | CData of CData.t
   | Spill of t * spill_info ref
   | Cast of t * ScopedTypeExpression.e
   and t = { it : t_; loc : Loc.t; ty : TypeAssignment.t MutableOnce.t }
  [@@ deriving show]

  let type_of { ty } : TypeAssignment.ty = assert(MutableOnce.is_set ty); TypeAssignment.deref ty

  open Format

  let lam = 0
  let app = 1

  let lvl_of = function
    | App(_, (_::_)) -> app
    | Var (_, (_::_)) -> app
    | Lam _ -> lam
    | _ -> 2

  let get_lam_name = function None -> F.from_string "_" | Some (n,_) -> n
  let mk_empty_lam_type = function
    | None -> None
    | Some (name, loc, scope) -> Some (mk_const name ~scope ~loc)

  (* The type of the object being constructed is irrelevant since 
    build_infix_constant is used in the pretty printer of term and the type
    of infix constants is not displayed
  *)
  let build_infix_constant name loc : t = {loc; ty = MutableOnce.make (F.from_string "dummy"); it = App(name,[]) }

  let is_infix_constant f =
    let infix = [F.andf; F.orf; F.eqf; F.isf; F.asf; F.consf] @ List.map F.from_string ["^";"+";"-";"*";"/"] in
    List.mem f infix

  let rec intersperse e : 'a -> t list = function
    | [] | [_] as a -> a
    | x::xs -> x :: e x.loc :: intersperse e xs

  let rec pretty_lam fmt n ste it =
    (match n with
    | None -> Format.fprintf fmt "_"
    | Some { scope; name; ty } -> 
      fprintf fmt "@[<hov 2>%a" F.pp name;
      if MutableOnce.is_set ty then
        fprintf fmt ": @[%a@] " TypeAssignment.pretty_mut_once (TypeAssignment.deref ty)
      else Option.iter (fprintf fmt ": %a " ScopedTypeExpression.pretty_e) ste);
      fprintf fmt "\\@]@ %a" pretty it;

  and pretty fmt { it } = pretty_ fmt it
  and pretty_ fmt = function
    | Impl(L2R,_,t1,t2) -> fprintf fmt "@[<hov 2>(%a =>@ (%a))@]" pretty t1 pretty t2
    | Impl(L2RBang,_,t1,t2) -> fprintf fmt "@[<hov 2>(%a =!=>@ (%a))@]" pretty t1 pretty t2
    | Impl(R2L,_,t1,t2) -> fprintf fmt "@[<hov 2>(%a :-@ %a)@]" pretty t1 pretty t2
    | App({ name = f },[]) -> fprintf fmt "%a" F.pp f
    | Discard -> fprintf fmt "_"
    | Lam(n, ste, it) -> pretty_lam fmt n ste it
    | App({ name = f },[x]) when F.equal F.spillf f -> fprintf fmt "{%a}" pretty x
    | App({ name = f },x::xs) when F.equal F.pif f || F.equal F.sigmaf f -> fprintf fmt "@[<hov 2>%a@ %a@]" F.pp f (Util.pplist ~pplastelem:(pretty_parens_lam ~lvl:app)  (pretty_parens ~lvl:app) " ") (x::xs)
    | App({ scope = Global _; name = f } as n,x::xs) when is_infix_constant f -> fprintf fmt "%a" (Util.pplist ~boxed:true (pretty_parens ~lvl:0) " ") (intersperse (build_infix_constant n) (x::xs))
    | App({ name = f },x::xs) -> fprintf fmt "@[<hov 2>%a@ %a@]" F.pp f (Util.pplist ~boxed:true (pretty_parens ~lvl:app) " ") (x::xs)
    | Var({ name = f },[]) -> fprintf fmt "@[%a@]" F.pp f
    | Var({ name = f },xs) -> fprintf fmt "@[%a@ %a@]" F.pp f (Util.pplist ~boxed:true (pretty_parens ~lvl:app) " ") xs
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

  let equal env ?(types=true) t1 t2 =
    let rec eq ctx t1 t2 =
      match t1.it, t2.it with
      | Discard, Discard -> true
      | Var(n1,l1), Var(n2,l2) -> eq_uvar ctx n1.name n2.name && Util.for_all2 (eq ctx) l1 l2
      | App({ scope = Global _ as b1; name = c1},xs), App({ scope = Global _ as b2; name = c2 },ys) -> Scope.equal env b1 b2 && F.equal c1 c2 && Util.for_all2 (eq ctx) xs ys
      | App({ scope = Bound l1; name = c1 },xs), App({ scope = Bound l2; name = c2 },ys) -> l1 = l2 && eq_var ctx l1 c1 c2 && Util.for_all2 (eq ctx) xs ys
      | Lam(None, ty1,b1), Lam (None,ty2, b2) -> eq ctx b1 b2 && (not types || Option.equal (ScopedTypeExpression.eqt env (empty ())) ty1 ty2)
      | Lam(Some { scope = l1; name = c1 },ty1,b1), Lam(Some { scope = l2; name = c2 },ty2, b2) -> l1 = l2 && eq (push_ctx l1 c1 c2 ctx) b1 b2 && (not types || Option.equal (ScopedTypeExpression.eqt env (empty ())) ty1 ty2)
      | Spill(b1,n1), Spill (b2,n2) -> n1 == n2 && eq ctx b1 b2
      | CData c1, CData c2 -> CData.equal c1 c2
      | Cast(t1,ty1), Cast(t2,ty2) -> eq ctx t1 t2 && (not types || ScopedTypeExpression.eqt env (empty ()) ty1 ty2)
      | Impl(b1,_,s1,t1), Impl(b2,_,s2,t2) -> b1 = b2 && eq ctx t1 t2 && eq ctx s1 s2
      | _ -> false
    in
      let b = eq (empty ()) t1 t2 in
      b

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
    | Impl(b,loc,t1,t2) -> Impl(b,loc,of_simple_term_loc t1, of_simple_term_loc t2)
    | Const(scope,c) -> App (mk_const ~scope c ~loc,[])
    | Opaque c -> CData c
    | Cast(t,ty) -> Cast(of_simple_term_loc t, ScopedTypeExpression.of_simple_type_loc ty)
    | Lam(c,ty,t) -> Lam(mk_empty_lam_type c,Option.map ScopedTypeExpression.of_simple_type_loc ty, of_simple_term_loc t)
    | App(s,c,cloc,x,xs) when SimpleTerm.is_implf c ->
      begin match xs with
        | [y] -> Impl(SimpleTerm.func_to_impl_kind c,cloc,of_simple_term_loc x, of_simple_term_loc y)
        | _ -> error ~loc "Use of App for Impl is allowed, but the length of the list in 3rd position must be 1"
      end
    | App(s,c,cloc,x,xs) -> App(mk_const ~scope:s c ~loc, of_simple_term_loc x :: List.map of_simple_term_loc xs)
    | Var(c,cloc,xs) -> Var(mk_bound_const ~lang:elpi_var c ~loc:cloc,List.map of_simple_term_loc xs)
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
      | Impl(b,loc,t1,t2) -> Impl(b,loc,rename_loc l c d t1, rename_loc l c d t2)
     | App({ scope = Bound l'; name = c';ty;loc},xs) when l = l' && F.equal c c' ->
          (* NOTE: the name in mutable once should be renamed *)
          App({scope = Bound l; name = d; ty; loc}, List.map (rename_loc l c d) xs)
      | App(n,xs) -> App(n, List.map (rename_loc l c d) xs)
      | Lam(Some { scope = l'; name = c'},_,_) when l = l' && F.equal c c' -> t
      | Lam(v,tya,t) -> Lam(v,tya,rename_loc l c d t)
      | Spill(t,i) -> Spill(rename_loc l c d t,i)
      | Cast(t,ty) -> Cast(rename_loc l c d t,ty)
      | Var(v,xs) -> Var(v,List.map (rename_loc l c d) xs)
      | Discard | CData _ -> t
    and rename_loc l c d { it; ty; loc } = { it = rename l c d it; ty; loc } 

    let rec clone_loc ~loc {it} = {it=clone ~loc it;loc;ty=TypeAssignment.new_ty ()} and
    clone ~loc = function
      | Impl (b, loc, l, r) -> Impl(b, loc, clone_loc ~loc l, clone_loc ~loc r)
      | Lam (n,ty,bo) -> Lam(Option.map clone_const n, ty, clone_loc ~loc bo)
      | Discard -> Discard
      | Var (v, xs) -> Var (clone_const v, List.map (clone_loc ~loc) xs)
      | App (g, xs) -> App (clone_const g, List.map (clone_loc ~loc) xs)
      | CData _ as t -> t 
      | Spill (t, _) -> Spill (clone_loc ~loc t, ref NoInfo)
      | Cast (t, ty) -> Cast (clone_loc ~loc t, ty)

    let beta t args =
      let rec fv acc { it } =
        match it with
        | Impl(_,_,a,b) -> List.fold_left fv acc [a;b]
        | Var (_,args) -> List.fold_left fv acc args
        | App({ scope = Bound l; name = c },xs) -> List.fold_left fv (Scope.Set.add (c,l) acc) xs
        | App({ scope = Global _ },xs) -> List.fold_left fv acc xs
        | Lam(None,_,t) -> fv acc t
        | Lam(Some { scope = c; name = l },_,t) -> Scope.Set.union acc @@ Scope.Set.remove (l,c) (fv Scope.Set.empty t)
        | Spill(t,_) -> fv acc t
        | Cast(t,_) -> fv acc t
        | Discard | CData _ -> acc in
      let rec load_subst ~loc t (args : t list) map fvset =
        match t, args with
        | Lam(None,_,t), _ :: xs -> load_subst_loc t xs map fvset
        | Lam(Some { scope = l; name = c },_,t), x :: xs -> load_subst_loc t xs (Scope.Map.add (c,l) x map) (fv fvset x)
        | t, xs -> app ~loc (subst map fvset t) xs
      and load_subst_loc { it; loc } args map fvset =
        load_subst ~loc it args map fvset
      and subst (map : t Scope.Map.t) fv t =
        match t with
        | Impl(b,loc,t1,t2) -> Impl(b,loc,subst_loc map fv t1, subst_loc map fv t2)
        | Lam(None,ty,t) -> Lam(None,ty,subst_loc map fv t)
        | Lam(Some { scope = c; name = l } as n,ty,t) when not @@ Scope.Map.mem (l,c) map && not @@ Scope.Set.mem (l,c) fv ->
            Lam(n,ty,subst_loc map fv @@ t)
        | Lam(Some { scope = l; name = c; ty = tya;loc },ty,t) ->
            let d = fresh () in
            Lam(Some { scope = l; name = d; ty = tya; loc },ty,subst_loc map fv @@ rename_loc l c d t)
        | App({ scope = Bound l; name = c },xs) when Scope.Map.mem (c,l) map ->
            let hd = Scope.Map.find (c,l) map in
            unlock @@ app_loc hd (List.map (subst_loc map fv) xs)
        | App(n,xs) -> App(n,List.map (subst_loc map fv) xs)
        | Var(c,xs) -> Var(c,List.map (subst_loc map fv) xs)
        | Spill(t,i) -> Spill(subst_loc map fv t,i)
        | Cast(t,ty) -> Cast(subst_loc map fv t,ty)
        | Discard | CData _ -> t
      and subst_loc map fv { it; ty; loc } = {loc; it = (subst map fv it); ty}
      and app_loc { it; loc; ty } args : t = {loc; it = (app ~loc it args); ty}
      and app ~loc t (args : t list) =
        if args = [] then t else
        match t with
        | App(n,xs) -> App(n,xs @ args)
        | Var(c,xs) -> Var(c,xs @ args)
        | Impl(_,_,_,_) -> error ~loc "cannot apply impl"
        | CData _ -> error ~loc "cannot apply cdata"
        | Spill _ -> error ~loc "cannot apply spill"
        | Discard -> error ~loc "cannot apply discard"
        | Cast _ -> error ~loc "cannot apply cast"
        | Lam _ -> load_subst ~loc t args Scope.Map.empty Scope.Set.empty
      in
        if args = [] then unlock t else
        load_subst_loc t args Scope.Map.empty Scope.Set.empty

  let beta t args =
    (* Format.eprintf "beta %a\n" pretty t; *)
    let t = beta t args in
    (* Format.eprintf "beta result %a\n" pretty_ t; *)
    t


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
            | { it = App({ scope = Bound g } as n,[]); loc = loc'; ty } when g = elpi_language ->
                { SimpleTerm.loc; it = SimpleTerm.Opaque (in_scoped_term @@ { it = App(n, l); loc = loc'; ty }) }
            | x -> anomaly ~loc (Format.asprintf "The term is not an elpi varible coming from a quotation: @[%a@]" pretty x)
            end
        | x -> anomaly ~loc (Format.asprintf "The term is not term coming from a quotation: @[%a@]" pp_t_ x)
  
  
    let extend_spill_hyp_from_quotation { SimpleTerm.it; loc } hyps =
      match it with
      | SimpleTerm.Opaque o when is_scoped_term o ->
          begin match out_scoped_term o with
          | { it = Spill(t,i); loc } ->
            let impl = { loc; it = Impl(L2R, loc, list_to_lp_list ~loc hyps, { loc; it = Opaque (in_scoped_term t) }) } in
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


module ScopeTypeExpressionUniqueList = struct

  type t = ScopedTypeExpression.t list
  [@@deriving show, ord]
  let pretty fmt l = pplist ScopedTypeExpression.pretty ";" fmt l
  
  let make t = [t]
    
  let smart_map = smart_map
  
  let append env x t = x :: List.filter (fun y -> not @@ ScopedTypeExpression.equal env x y) t
  let merge env t1 t2 = List.fold_left (fun acc x -> append env x acc) (List.rev t1) t2

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
