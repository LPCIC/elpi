open Ppxlib
open Ppxlib.Ast_pattern

(**

  Deriving directives:

    [@@deriving elpi] Simple ADT.
    [@@deriving elpi { index = (module M) }] Context ADT.
       M is an OrderedType and Show, it is used to instantiate the
       functor Elpi.Utils.Map.Make.
       All constructors must have 1 argument with attribute [@elpi.key]
       and that argument must be of type M.t
    [@@deriving elpi { context = (() : ty) }] HOADT.
       Its context is represented by items of the context ADT ty, if ty is a
       type name.
       If ty is of the form "(ty1 -> ctx1) * .. * (tyn -> ctxn)" then the
       context is represented by items of (the union of) the context ADTs
       ctx1 ... ctxn. ": ty" stands for ": (current_type -> ty)".
       Constructors can have the [@elpi.var] attribute and
       constructor arguments can have the [@elpi.binder] attribute
    [@@deriving elpi { append = l }]
       appends to list (l : Elpi.API.BuiltIn.declaration list ref)
       all data types that were derived

    In all cases the type must come with a pretty printer named following the
    ppx_deriving.show convention (named pp if the type is named t, pp_ty
    otherwise). Using both [@@derving show, elpi] on each data type is
    the simplest option.

*)
let pexp_ignore = Deriving.Args.of_func (fun _ _ (_e : expression) b -> b)

let arguments = Deriving.Args.(empty
  +> arg "index" (pexp_pack __)
  +> arg "context" (pexp_constraint pexp_ignore __)
  +> arg "append" __
)
(**
  Type attributes:

    [@@elpi.code]
      see the constructor attribute with the same name
    [@@elpi.doc]
      see the constructor attribute with the same name
    [@@elpi.default_readback]
      the default case can be used to read back flexible terms. The default is
      a runtime type error
    [@@elpi.pp]
      code for pretty printing the data. Type is the one ppx_deriving.show
      would produce
*)
let att_elpi_tcode     = Attribute.(declare "elpi.code"     Context.type_declaration (single_expr_payload __) (fun x -> x))
let att_elpi_tdoc      = Attribute.(declare "elpi.doc"      Context.type_declaration (single_expr_payload (estring __)) (fun x -> x))
let att_elpi_treadback = Attribute.(declare "elpi.default_readback" Context.type_declaration (single_expr_payload __) (fun x -> x))
let att_elpi_pp        = Attribute.(declare "elpi.pp" Context.type_declaration (single_expr_payload __) (fun x -> x))
(**
  Constructor attributes:

    [@elpi.var] An Elpi bound variable.
      Optional argument is a function from the constructor arguments to the
      type being the [@elpi.key] for the context.
    [@elpi.skip] Not exposed to Elpi.
    [@elpi.embed] Custom embedding code.
      Argument of type Elpi.API.ContextualConversion.embedding
    [@elpi.readback] Custom readback code.
      Argument of type Elpi.API.ContextualConversion.embedding
    [@elpi.code] Custom Elpi declaration.
      First argument is a string and stands for the name of the type
      constructor. The default is the name of the OCaml constructor in lowercase
      where _ is replaced by - . Eg Foo_BAR becomes foo-bar.
      Second argument is optional and is a string used as the Elpi type
      for the constructor. Default is derived from the types of the fields.
    [@elpi.doc] Custom documentation.
      Argument is a string. Default doc is the name of the OCaml constructor
*)
let att_elpi_var      = Attribute.(declare "elpi.var"      Context.constructor_declaration (alt_option (single_expr_payload __) (pstr nil)) (fun x -> x))
let att_elpi_skip     = Attribute.(declare "elpi.skip"     Context.constructor_declaration (pstr nil) ())
let att_elpi_embed    = Attribute.(declare "elpi.embed"    Context.constructor_declaration (single_expr_payload __) (fun x -> x))
let att_elpi_readback = Attribute.(declare "elpi.readback" Context.constructor_declaration (single_expr_payload __) (fun x -> x))
let att_elpi_code     = Attribute.(declare "elpi.code"     Context.constructor_declaration (single_expr_payload __) (fun x -> x))
let att_elpi_doc      = Attribute.(declare "elpi.doc"      Context.constructor_declaration (single_expr_payload (estring __)) (fun x -> x))
(**

  Constructor field attribute:

    [@elpi.key] Field used as a key in the Map to values of this type.
    [@elpi.binder] Field is below one binder.
      First argument is optional and is a string (or an ident) and is the type
      of the bound variable. Default value is the type to which [@@elpi : ty]
      is applied.
      Second argument is a function taking all other fields and returning
      a ctx entry (a value in the type ty of [@@elpi : ty])
*)
let att_elpi_key    = Attribute.(declare "elpi.key"    Context.core_type (pstr nil) ())
let att_elpi_binder = Attribute.(declare "elpi.binder" Context.core_type (single_expr_payload __) (fun x -> x))
(**
  Extensions:

    [%elpi : ty] the conversion of type ty

  Conventions:

    <ty> is a value of type Elpi.API.ContextualConversion.t for type ty.

    in_<ty> is a value of type Elpi.API.ContextualConversion.ctx_readback
    for type <ty>. It exists only for context ADTs.

    Elpi_<ctx>_Map is a module of signature Elpi.API.Utils.Map.S built using
    Elpi.API.Utils.Map.Make(M) where type ctx is a context ADT annotated as
    [@@elpi (module M)]. It exists only for context ADTs.

    TODO: elpi_push_xxx elpi_pop_xxx elpi_xxx_state elpi_xxx_to_key elpi_xxx

  Internal conventions:

    Variables are named elpi__something so that they don't collide with
    any variable named elpi_something or something.

 *)
 let elpi_name_mangle txt =
  String.map (function '_' -> '-' | x -> x) @@
  String.lowercase_ascii txt
let elpi_map_name x = "Elpi_"^x^"_Map"
let elpi_state_name x = "elpi_"^x^"_state"
let elpi_in_name_alone x = "in_" ^ x ^ "_alone"
let elpi_in_name x = "in_" ^ x
let elpi_to_key x = "elpi_" ^ x ^ "_to_key"
let elpi_is_ctx_entry_name x = "elpi_is_" ^ x
let elpi_embed_name x = "elpi_embed_" ^ x
let elpi_readback_name x = "elpi_readback_" ^ x
let elpi_push x = "elpi_push_" ^ x
let elpi_pop x = "elpi_pop_" ^ x
let elpi_kname t k = "elpi_constant_constructor_" ^ t ^ "_" ^ k ^ "c"
let elpi_tname t = "elpi_constant_type_" ^ t ^ "c"
let elpi_kname_str t k = "elpi_constant_constructor_" ^ t ^ "_" ^ k
let elpi_tname_str t = "elpi_constant_type_" ^ t
let param_prefix = "elpi__param__"
let fresh =
  let x = ref 0 in
  fun () -> incr x; Printf.sprintf "elpi__%d" !x
let elpi_Map ~loc x f = Ast_builder.Default.evar ~loc ("Elpi_"^x^"_Map." ^ f)


let is_some = function Some _ -> true | _ -> false
let option_get = function Some x -> x | _ -> assert false
let option_map f = function Some x -> Some (f x) | _ -> None
let option_default d = function Some x -> x | _ -> d
let rec filter_map f = function
  | [] -> []
  | x :: xs ->
      match f x with
      | None -> filter_map f xs
      | Some y -> y :: filter_map f xs

let error ?loc = Location.raise_errorf ?loc
let nYI ~loc ~__LOC__ () = error ~loc "nYI: %s" __LOC__

let elpi_loc_of_position (module B : Ast_builder.S) pos = let open B in
  let open Location in
  let open Lexing in
  [%expr {
    Elpi.API.Ast.Loc.source_name = [%e estring @@ pos.pos_fname ];
    source_start                 = [%e eint    @@ pos.pos_cnum  ];
    source_stop                  = [%e eint    @@ pos.pos_cnum  ];
    line                         = [%e eint    @@ pos.pos_lnum  ];
    line_starts_at               = [%e eint    @@ pos.pos_bol   ];
  }]

(*
let get_attr_expr s l =
  match find_attr_expr s l with
  | None -> error ("attribute " ^ s ^ " with no payload")
  | Some e -> e
*)



let pexp_disable_warnings (module B : Ast_builder.S) x =
  [%expr [%e x ][@warning "-26-27-32-39-60"]]

let abstract_expr_over_params (module B : Ast_builder.S) vl f e = let open B in
  let rec aux = function
    | [] -> e
    | v :: vs -> [%expr fun [%p pvar (f v) ] -> [%e aux vs]]
  in
    aux vl

let rec on_last f = function
  | [] -> assert false
  | [x] -> [f x]
  | y :: ys -> y :: on_last f ys

type directive =
  | Standard
  | Custom of expression * position
  | Name of expression
let is_name = function Name _ -> true | _ -> false

type arg_type =
  | FO of {
      argFO_key : bool;
      argFO_readback : expression;
      argFO_embed : expression;
      argFO_ty_ast : expression;
      argFO_ty : core_type;
   }
  | HO of {
      argHO_arrow_src : string;
      argHO_build_ctx : expression;
      argHO_readback : expression;
      argHO_embed : expression; (* if context = SOMe map, then store here which component of the state one has to pick *)
      argHO_ty_ast : expression;
      argHO_ty : core_type;
    }
let is_key = function FO { argFO_key = k; _ } -> k | _ -> false
let is_HO = function HO _ -> true | _ -> false

let ctx_index_ty (module B : Ast_builder.S) = let open B in
  FO {
    argFO_readback = [%expr Elpi.API.PPX.readback_nominal ];
    argFO_embed    = [%expr Elpi.API.PPX.embed_nominal ];
    argFO_ty_ast   = [%expr Elpi.API.PPX.nominal.Elpi.API.ContextualConversion.ty ];
    argFO_ty = [%type: int];
    argFO_key = false;
  }

type elpi_constructor =
  | Skip of { constructor_name : string; has_args : bool }
  | Expose of expose
and expose = {
      declaration : structure_item list;
      constant : expression;
      constant_name : string;
      constructor : expression list -> expression;
      pattern : pattern list -> pattern;
      types : arg_type list;
      embed : directive;
      readback : directive;
      elpi_code : expression option; (* string *)
      elpi_doc : string;
    }

type elpi_type_decl =
  | Opaque
  | Alias of core_type
  | Algebraic of elpi_constructor list * expression option (* default readback *)

type elpi_type = {
    name : string;
    elpi_name : string;
    elpi_code : string option;
    elpi_doc : string;
    params : string list;
    type_decl : elpi_type_decl;
    pp : expression option;
  }

type task_kind = ADT | CTX of module_expr * string list | HOAS of (string * string) list
type task = elpi_type * task_kind

type type_extras = {
  ty_constants : structure_item list;
  ty_embed : value_binding;
  ty_readback : value_binding;
  ty_conversion : value_binding;
  ty_conversion_name : string;
  ty_context_helpers : structure_item list;
  ty_context_readback : structure_item list;
  ty_elpi_declaration : elpi_declaration;
  ty_opaque : bool;
  ty_library : expression option; (* should be Elpi AST *)
}
and elpi_declaration = {
  decl : structure_item;
  decl_name : expression
}

let ctx_for k = function
  | None -> assert false
  | Some l ->
      try List.assoc k l
      with Not_found ->
        error "cannot find context type for %s" k

let rec drop_skip = function
  | [] -> []
  | Skip _ :: l -> drop_skip l
  | Expose x :: l -> x :: drop_skip l
let rec keep_skip = function
  | [] -> []
  | Skip { constructor_name; has_args } :: l -> (constructor_name, has_args) :: keep_skip l
  | Expose _ :: l -> keep_skip l

let rec list_take i = function
  | [] -> []
  | _ :: _ when i = 0 -> []
  | x :: xs -> x :: list_take (i-1) xs

let rec embed_k (module B : Ast_builder.S) ctx c all_kargs all_tmp kargs tmp tys n = let open B in
  match kargs, tmp, tys with
  | [], [], [] ->
    [%expr elpi__state, Elpi.API.RawData.mkAppL [%e c] [%e elist @@ List.map evar @@ List.map fst all_kargs], List.concat [%e elist all_tmp] ]
  | (px,ex) :: xs, y :: ys, (FO { argFO_embed = t; _ }) :: ts -> [%expr
      let elpi__state, [%p pvar px], [%p pvar y] =
        [%e t] ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state [%e ex] in
      [%e embed_k (module B) ctx c all_kargs all_tmp xs ys ts (n+1)]]
  | (px,ex) :: xs, y :: ys, HO{ argHO_build_ctx = f; argHO_embed = t; argHO_arrow_src = src; _ } :: ts ->
      let xtmp = fresh () in
      let ctx_name = ctx_for src ctx in
      let elpi_to_key = evar (elpi_to_key ctx_name) in
      let elpi_push = evar (elpi_push ctx_name) in
      let elpi_pop = evar (elpi_pop ctx_name) in
      [%expr
      let elpi__ctx_entry = [%e eapply f (List.map snd @@ list_take n all_kargs) ] in
      let elpi__ctx_key = [%e elpi_to_key ] ~depth: elpi__depth elpi__ctx_entry in
      let elpi__ctx_entry = { Elpi.API.ContextualConversion.entry = elpi__ctx_entry; depth = elpi__depth } in
      let elpi__state = [%e elpi_push ] ~depth: (elpi__depth + 1) elpi__state elpi__ctx_key elpi__ctx_entry in
      let elpi__state, [%p pvar xtmp], [%p pvar y] =
        [%e t] ~depth: (elpi__depth + 1) elpi__hyps elpi__constraints elpi__state [%e ex] in
      let [%p pvar px] = Elpi.API.RawData.mkLam [%e evar xtmp] in
      let elpi__state = [%e elpi_pop ] ~depth: (elpi__depth + 1) elpi__state elpi__ctx_key in
      [%e embed_k (module B) ctx c all_kargs all_tmp xs ys ts (n+1)]]
  | _ -> assert false
;;

let embed_var (module B : Ast_builder.S) ctx_name args p = let open B in
  let elpi_Map = elpi_Map ~loc ctx_name in
  [%expr
   let elpi__ctx2dbl, _ = Elpi.API.State.get [%e evar (elpi_state_name ctx_name)] elpi__state in
   let elpi__key = [%e eapply p args] in
   if not ([%e elpi_Map "mem" ] elpi__key elpi__ctx2dbl) then
     Elpi.API.Utils.error "Unbound variable";
   elpi__state, Elpi.API.RawData.mkBound ([%e elpi_Map "find" ] elpi__key elpi__ctx2dbl), []
 ]

let error_constructor_not_supported (module B : Ast_builder.S) (constructor,has_args) = let open B in
     case ~guard:None ~lhs:(ppat_construct (Located.lident constructor) (if has_args then Some (pvar "_") else None))
       ~rhs:[%expr Elpi.API.Utils.error ("constructor "^[%e estring constructor]^" is not supported") ]

let abstract_standard_branch_embed (module B : Ast_builder.S) l e = let open B in
  let rec aux = function
    | [] -> e
    | x::xs -> [%expr fun [%p pvar x] -> [%e aux xs]]
  in
  [%expr fun ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state -> [%e aux l ]]

let embed_branch (module B : Ast_builder.S) name (is_pred,ctx) = function
 | Skip { constructor_name; has_args } -> error_constructor_not_supported (module B) (constructor_name,has_args)
 | Expose { constant; types; embed; pattern; _ } -> let open B in
  let pvl, pattern, types =
    let pvl = List.map (fun _ -> fresh()) types in
    let kpattern = pattern (List.map pvar pvl) in
    if is_pred then
       let idx = fresh () in
       idx :: pvl, ppat_tuple [pvar idx;kpattern], ctx_index_ty (module B) :: types
    else pvl, kpattern, types in
  let standard =
    let evl = List.map (fun _ -> fresh()) types in
    let pvl2 = List.map (fun x -> fresh (), evar x) pvl in
    embed_k (module B) ctx constant pvl2 (List.map evar evl) pvl2 evl types 0 in
 case ~guard:None ~lhs:pattern
    ~rhs:begin match embed with
    | Custom (e,_) ->
        eapply [%expr [%e e] [%e abstract_standard_branch_embed (module B) pvl standard ]
             ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state] (List.map evar pvl)
    | Standard -> standard
    | Name p ->
           let ctx_name = ctx_for name ctx in
           embed_var (module B) ctx_name (List.map evar pvl) p
    end

let embed (module B : Ast_builder.S) name job kl = let open B in
    [%expr fun ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state ->
      [%e pexp_function (List.map (embed_branch (module B) name job) kl) ]]

let readback_k (module B : Ast_builder.S) c ctx mk_k t ts = let open B in
  let one all_kargs n p1 e1 t x kont =
    match t with
    | FO { argFO_readback = t; _ } -> [%expr
        let elpi__state, [%p pvar p1], [%p pvar e1] =
          [%e t] ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state [%e x] in
        [%e kont] ]
    | HO { argHO_build_ctx = f; argHO_readback = t; argHO_arrow_src = src; _ } ->
      let ctx_name = ctx_for src ctx in
      let elpi_to_key = evar (elpi_to_key ctx_name) in
      let elpi_push = evar (elpi_push ctx_name) in
      let elpi_pop = evar (elpi_pop ctx_name) in
      [%expr
        let elpi__ctx_entry = [%e eapply f (List.map evar @@ list_take n all_kargs) ] in
        let elpi__ctx_key = [%e elpi_to_key ] ~depth: elpi__depth elpi__ctx_entry in
        let elpi__ctx_entry = { Elpi.API.ContextualConversion.entry = elpi__ctx_entry; depth = elpi__depth } in
        let elpi__state = [%e elpi_push ] ~depth: elpi__depth elpi__state elpi__ctx_key elpi__ctx_entry in
        let elpi__state, [%p pvar p1], [%p pvar e1] =
          match Elpi.API.RawData.look ~depth: elpi__depth [%e x] with
          | Elpi.API.RawData.Lam elpi__bo ->
                [%e t] ~depth: (elpi__depth + 1) elpi__hyps elpi__constraints elpi__state elpi__bo
          | _ -> assert false in
       let elpi__state = [%e elpi_pop ] ~depth: elpi__depth elpi__state elpi__ctx_key in
       [%e kont]] in
  let rec roll_readback all_kargs n all_tmp kargs tmp tys =
    match kargs, tmp, tys with
    | [], [], [] ->
       [%expr (elpi__state, [%e mk_k (List.map evar all_kargs)], List.concat [%e elist @@ List.map evar all_tmp]) ]
    | x :: xs, y :: ys, t :: ts ->
       one all_kargs n x y t (evar x) (roll_readback all_kargs (n+1) all_tmp xs ys ts)
    | _ -> assert false
    in
  let rec roll_pat = function
    | [] -> [%pat? [] ]
    | x :: xs -> [%pat? [%p pvar x] :: [%p roll_pat xs] ] in
  let ps = List.map (fun _ -> fresh()) ts in
  let es = List.map (fun _ -> fresh()) ts in
  let p1, e1 = fresh (), fresh () in
  let all_kargs = p1 :: ps in
    one all_kargs 0 p1 e1 t [%expr elpi__x] [%expr
      match elpi__xs with
      | [%p roll_pat ps ] ->
          [%e roll_readback all_kargs 1 (e1 :: es) ps es ts]
      | _ -> Elpi.API.Utils.type_error
              ("Not enough arguments to constructor: " ^ Elpi.API.RawData.Constants.show [%e c])
    ]

let readback_var (module B : Ast_builder.S) ctx_name constructor = let open B in
  let elpi_to_key = evar (elpi_to_key ctx_name) in
  let elpi_state_component = evar (elpi_state_name ctx_name) in
  [%expr
    let _, elpi__dbl2ctx = Elpi.API.State.get [%e elpi_state_component ] elpi__state in
    if not (Elpi.API.RawData.Constants.Map.mem elpi__hd elpi__dbl2ctx) then
      Elpi.API.Utils.error (Format.asprintf "Unbound variable: %s in %a"
        (Elpi.API.RawData.Constants.show elpi__hd)
        (Elpi.API.RawData.Constants.Map.pp (Elpi.API.ContextualConversion.pp_ctx_entry [%e evar ("pp_" ^ ctx_name)])) elpi__dbl2ctx);
    let { Elpi.API.ContextualConversion.entry = elpi__entry; depth = elpi__depth } = Elpi.API.RawData.Constants.Map.find elpi__hd elpi__dbl2ctx in
    elpi__state, [%e constructor [ [%expr [%e elpi_to_key ] ~depth: elpi__depth elpi__entry ] ] ], []
  ]

let abstract_standard_branch_readback (module B : Ast_builder.S) pos e = let open B in
   [%expr fun ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state -> function
      | [] -> [%e e ]
      | _ -> Elpi.API.Utils.error ~loc: [%e elpi_loc_of_position (module B) pos ] "standard branch readback takes 0 arguments"]

let abstract_standard_branch_readback2 (module B : Ast_builder.S) pos e = let open B in
   [%expr fun ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state -> function
     | elpi__x :: elpi__xs -> [%e e ]
     | [] -> Elpi.API.Utils.error ~loc: [%e elpi_loc_of_position (module B) pos ] "standard branch readback takes 1 argument or more"]

let readback_branch (module B : Ast_builder.S) name (is_pred,ctx) { constant; constructor; types; readback; _ } = let open B in
  let types, mk_k =
    if is_pred then ctx_index_ty (module B) :: types, (function x :: xs -> pexp_tuple [x;constructor xs] | [] -> assert false)
    else types, constructor in
  match types with
  | [] ->
      let standard = [%expr elpi__state, [%e constructor [] ], []] in
      case ~lhs:[%pat? Elpi.API.RawData.Const elpi__hd]
               ~guard:(Some [%expr elpi__hd == [%e constant]])
        ~rhs:begin match readback with
        | Standard -> standard
        | Custom(e,pos) -> [%expr [%e e] [%e abstract_standard_branch_readback (module B) pos standard] ~depth: elpi__depth elpi__hyps elpi__constraints [] ]
        | Name _ -> assert false
        end
  | t :: ts ->
      let standard = readback_k (module B) constant ctx mk_k t ts in
      match readback with
      | Standard ->
          case ~lhs:[%pat? Elpi.API.RawData.App (elpi__hd,elpi__x,elpi__xs)]
               ~guard:(Some [%expr elpi__hd == [%e constant]])
               ~rhs:standard
      | Custom(e,pos) ->
          case ~lhs:[%pat? Elpi.API.RawData.App (elpi__hd,elpi__x,elpi__xs)]
               ~guard:(Some [%expr elpi__hd == [%e constant]])
               ~rhs:([%expr [%e e] [%e abstract_standard_branch_readback2 (module B) pos standard ] ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state (elpi__x :: elpi__xs)])
      | Name _ -> assert(ts = []);
          let ctx_name = ctx_for name ctx in
          case ~lhs:[%pat? Elpi.API.RawData.Const elpi__hd]
              ~guard:(Some [%expr elpi__hd >= 0])
              ~rhs:(readback_var (module B) ctx_name constructor)

let abstract_standard_default_readback (module B : Ast_builder.S) e = let open B in
  [%expr fun ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x -> [%e e]]

let readback (module B : Ast_builder.S) name job default_readback kl = let open B in
    [%expr fun ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x ->
      [%e pexp_match [%expr Elpi.API.RawData.look ~depth: elpi__depth elpi__x]
        (List.map (readback_branch (module B) name job) (drop_skip kl) @
        [case ~guard:None ~lhs:[%pat? _ ]
          ~rhs:begin
            let standard =
              [%expr Elpi.API.Utils.type_error (Format.asprintf "Not a constructor of type %s: %a"
                 [%e estring name] (Elpi.API.RawPp.term elpi__depth) elpi__x) ] in
            match default_readback with
            | None -> standard
            | Some e -> [%expr [%e e] [%e abstract_standard_default_readback (module B) standard ] ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x ]
            end])]]

let ctx_entry_key (module B : Ast_builder.S) kl = let open B in
  let project { pattern; types; _ } =
    let pvl = List.map (function FO { argFO_key = true; _ } -> fresh() | _ -> "_") types in
    let rec find_key vl tl =
      match vl, tl with
      | v :: _, FO { argFO_key = true; _ } :: _ -> evar v
      | _ :: vs, _ :: ts -> find_key vs ts
      | _ -> assert false in

    case ~lhs:(pattern (List.map pvar pvl)) ~guard:None ~rhs:(find_key pvl types) in
  [%expr fun ~depth:_ -> [%e pexp_function (
    List.map project (drop_skip kl) @
    List.map (error_constructor_not_supported (module B)) (keep_skip kl)) ] ]

let is_ctx_entry (module B : Ast_builder.S) kl = let open B in
  [%expr fun ~depth: elpi__depth elpi__x -> match  Elpi.API.RawData.look ~depth: elpi__depth elpi__x with
    | Elpi.API.RawData.Const _ -> None
    | Elpi.API.RawData.App(elpi__hd,elpi__idx,_) ->
      if [%e
        List.fold_left (fun e -> function
          | Skip _ -> e
          | Expose { constant; _ } ->
             [%expr [%e e] || elpi__hd == [%e constant]])
        [%expr false] kl
        ]
      then match  Elpi.API.RawData.look ~depth: elpi__depth elpi__idx with
        | Elpi.API.RawData.Const x -> Some x
        | _ -> Elpi.API.Utils.type_error "context entry applied to a non nominal"
      else None
    | _ -> None ]

let ctx_readback (module B : Ast_builder.S) name = let open B in
  let elpi_Map = elpi_Map ~loc name in
  let elpi_push = evar (elpi_push name) in
  let elpi_to_key = evar (elpi_to_key name) in
  let elpi_is_ctx_entry = evar (elpi_is_ctx_entry_name name) in
  let elpi_state_component = evar (elpi_state_name name) in
  [%expr fun ~depth: elpi__depth elpi__hyps elpi__constraints elpi__state ->
    let module CMap = Elpi.API.RawData.Constants.Map in
    let elpi__filtered_hyps =
      List.fold_left (fun elpi__m ({ Elpi.API.RawData.hdepth = elpi__i; hsrc = elpi__hsrc } as elpi__hyp) ->
        match [%e elpi_is_ctx_entry ] ~depth:elpi__i elpi__hsrc with
        | None -> elpi__m
        | Some elpi__idx ->
             if CMap.mem elpi__idx elpi__m then
               Elpi.API.Utils.type_error "more than one context entry for the same nominal";
             CMap.add elpi__idx elpi__hyp elpi__m
        ) CMap.empty (Elpi.API.RawData.of_hyps elpi__hyps) in
    let rec elpi__aux elpi__state elpi__gls elpi__i =
      if elpi__i = elpi__depth then
        elpi__state, List.concat (List.rev elpi__gls)
      else if not (CMap.mem elpi__i elpi__filtered_hyps) then
        elpi__aux elpi__state elpi__gls (elpi__i+1)
      else
        let elpi__hyp = CMap.find elpi__i elpi__filtered_hyps in
        let elpi__hyp_depth = elpi__hyp.Elpi.API.RawData.hdepth in
        let elpi__state, (elpi__nominal, elpi__t), elpi__gls_t =
          [%e evar name].Elpi.API.ContextualConversion.readback ~depth: elpi__hyp_depth elpi__hyps elpi__constraints elpi__state elpi__hyp.Elpi.API.RawData.hsrc in
        assert(elpi__nominal = elpi__i);
        let elpi__s = [%e elpi_to_key ] ~depth: elpi__hyp_depth elpi__t in
        let elpi__state = [%e elpi_push ] ~depth:elpi__i elpi__state elpi__s { Elpi.API.ContextualConversion.entry = elpi__t; depth = elpi__hyp_depth } in
        elpi__aux elpi__state (elpi__gls_t :: elpi__gls) (elpi__i+1) in
    let elpi__state = Elpi.API.State.set [%e elpi_state_component ] elpi__state
      ([%e elpi_Map "empty" ], CMap.empty) in
    let elpi__state, elpi__gls = elpi__aux elpi__state [] 0 in
  let _, elpi__dbl2ctx = Elpi.API.State.get [%e elpi_state_component ] elpi__state in
    elpi__state, elpi__dbl2ctx, elpi__constraints, elpi__gls]

let rec compose_ctx_readback (module B : Ast_builder.S) = function
  | [] -> assert false
  | [x] -> B.evar (elpi_in_name_alone x)
  | x :: xs -> let open B in 
               [%expr Elpi.API.ContextualConversion.(|+|)
                    [%e evar (elpi_in_name_alone x) ]
                    [%e compose_ctx_readback (module B) xs] ]

let ctx_push (module B : Ast_builder.S) name = let open B in
  let elpi_Map = elpi_Map ~loc name in
  [%expr fun ~depth:elpi__depth elpi__state elpi__name elpi__ctx_item ->
  let elpi__ctx2dbl, elpi__dbl2ctx = Elpi.API.State.get [%e evar (elpi_state_name name)] elpi__state in
  let elpi__i = elpi__depth in
  let elpi__ctx2dbl = [%e elpi_Map "add" ] elpi__name elpi__i elpi__ctx2dbl in
  let elpi__dbl2ctx = Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item elpi__dbl2ctx in
  let elpi__state = Elpi.API.State.set [%e evar (elpi_state_name name)] elpi__state (elpi__ctx2dbl, elpi__dbl2ctx) in
  elpi__state]

let ctx_pop (module B : Ast_builder.S) name = let open B in
  let elpi_Map = elpi_Map ~loc name in
  [%expr fun ~depth:elpi__depth elpi__state elpi__name ->
  let elpi__ctx2dbl, elpi__dbl2ctx = Elpi.API.State.get [%e evar (elpi_state_name name)] elpi__state in
  let elpi__i = elpi__depth in
  let elpi__ctx2dbl = [%e elpi_Map "remove" ] elpi__name elpi__ctx2dbl in
  let elpi__dbl2ctx = Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
  let elpi__state = Elpi.API.State.set [%e evar (elpi_state_name name)] elpi__state (elpi__ctx2dbl, elpi__dbl2ctx) in
  elpi__state]

let rec fmap f = function [] -> [] | x :: xs -> match f x with None -> fmap f xs | Some x -> x :: fmap f xs

let conversion_of (module B : Ast_builder.S)  ty = let open B in
  let rec aux = function
   | [%type: string] -> [%expr Elpi.API.ContextualConversion.(!>) Elpi.API.BuiltInData.string]
   | [%type: int]    -> [%expr Elpi.API.ContextualConversion.(!>) Elpi.API.BuiltInData.int]
   | [%type: float]  -> [%expr Elpi.API.ContextualConversion.(!>) Elpi.API.BuiltInData.float]
   | [%type: bool]   -> [%expr Elpi.API.ContextualConversion.(!>) Elpi.Builtin.bool]
   | [%type: char]   -> [%expr Elpi.API.ContextualConversion.(!>) Elpi.Builtin.char]
   | [%type: [%t? typ] list]          -> [%expr Elpi.API.ContextualConversion.(!>>) Elpi.API.BuiltInData.list [%e aux typ ]]
   | [%type: [%t? typ] option]        -> [%expr Elpi.API.ContextualConversion.(!>>) Elpi.Builtin.option [%e aux typ ]]
   | [%type: [%t? typ1] * [%t? typ2]] -> [%expr Elpi.API.ContextualConversion.(!>>>) Elpi.Builtin.pair [%e aux typ1 ] [%e aux typ2 ]]
   | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3]] -> [%expr Elpi.Builtin.triple [%e aux typ1 ]  [%e aux typ2 ] [%e aux typ3 ]]
   | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3] * [%t? typ4]] -> [%expr Elpi.Builtin.quadruple [%e aux typ1 ] [%e aux typ2 ] [%e aux typ3 ] [%e aux typ4 ]]
   | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3] * [%t? typ4] * [%t? typ5]] -> [%expr Elpi.Builtin.quintuple [%e aux typ1 ] [%e aux typ2 ] [%e aux typ3 ] [%e aux typ4 ] [%e aux typ5 ]]
   | { ptyp_desc = Ptyp_tuple _; _ } -> error ~loc "seriously? I don't have sixtuples at hand, file a bugreport"
   | { ptyp_desc = Ptyp_constr ({ txt = id; _ }, params); _ } ->
        let id = pexp_ident @@ Located.mk id in
        eapply id (List.map aux params)
   | t -> error ~loc "cannot compute conversion for type %a" Pprintast.core_type t
  in
    aux ty

let is_parameter id = Re.(Str.string_match (Str.regexp_string param_prefix) id 0)

let rec find_embed_of (module B : Ast_builder.S) current_mutrec_block  ty = let open B in
  let rec aux ty =
  match ty with
   | [%type: string] -> [%expr Elpi.API.PPX.embed_string]
   | [%type: int]    -> [%expr Elpi.API.PPX.embed_int]
   | [%type: float]  -> [%expr Elpi.API.PPX.embed_float]
   | [%type: bool]   -> [%expr Elpi.Builtin.PPX.embed_bool]
   | [%type: char]   -> [%expr Elpi.Builtin.PPX.embed_char]
   | [%type: [%t? typ] list]          -> [%expr Elpi.API.PPX.embed_list [%e aux typ ]]
   | [%type: [%t? typ] option]        -> [%expr Elpi.Builtin.PPX.embed_option [%e aux typ ]]
   | [%type: [%t? typ1] * [%t? typ2]] -> [%expr Elpi.Builtin.PPX.embed_pair [%e aux typ1 ] [%e aux typ2 ]]
   | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3]] -> [%expr Elpi.Builtin.PPX.embed_triple [%e aux typ1 ]  [%e aux typ2 ] [%e aux typ3 ]]
   | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3] * [%t? typ4]] -> [%expr Elpi.Builtin.PPX.embed_quadruple [%e aux typ1 ] [%e aux typ2 ] [%e aux typ3 ] [%e aux typ4 ]]
   | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3] * [%t? typ4] * [%t? typ5]] -> [%expr Elpi.Builtin.PPX.embed_quintuple [%e aux typ1 ] [%e aux typ2 ] [%e aux typ3 ] [%e aux typ4 ] [%e aux typ5 ]]
  | { ptyp_desc = Ptyp_constr ({ txt = Longident.Lident id; _ }, params); _ }
    when List.mem id current_mutrec_block || is_parameter id ->
      eapply (evar (elpi_embed_name id)) (List.map (find_embed_of (module B) current_mutrec_block) params)
  | t -> [%expr [%e conversion_of (module B) t ].Elpi.API.ContextualConversion.embed ]
  in
    aux ty

let rec find_readback_of (module B : Ast_builder.S) current_mutrec_block  ty = let open B in
  let rec aux ty =
  match ty with
   | [%type: string] -> [%expr Elpi.API.PPX.readback_string]
   | [%type: int]    -> [%expr Elpi.API.PPX.readback_int]
   | [%type: float]  -> [%expr Elpi.API.PPX.readback_float]
   | [%type: bool]   -> [%expr Elpi.Builtin.PPX.readback_bool]
   | [%type: char]   -> [%expr Elpi.Builtin.PPX.readback_char]
   | [%type: [%t? typ] list]          -> [%expr Elpi.API.PPX.readback_list [%e aux typ ]]
   | [%type: [%t? typ] option]        -> [%expr Elpi.Builtin.PPX.readback_option [%e aux typ ]]
   | [%type: [%t? typ1] * [%t? typ2]] -> [%expr Elpi.Builtin.PPX.readback_pair [%e aux typ1 ] [%e aux typ2 ]]
   | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3]] -> [%expr Elpi.Builtin.PPX.readback_triple [%e aux typ1 ]  [%e aux typ2 ] [%e aux typ3 ]]
   | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3] * [%t? typ4]] -> [%expr Elpi.Builtin.PPX.readback_quadruple [%e aux typ1 ] [%e aux typ2 ] [%e aux typ3 ] [%e aux typ4 ]]
   | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3] * [%t? typ4] * [%t? typ5]] -> [%expr Elpi.Builtin.PPX.readback_quintuple [%e aux typ1 ] [%e aux typ2 ] [%e aux typ3 ] [%e aux typ4 ] [%e aux typ5 ]]
  | { ptyp_desc = Ptyp_constr ({ txt = Longident.Lident id; _ }, params); _ }
    when List.mem id current_mutrec_block || is_parameter id ->
      eapply (evar (elpi_readback_name id)) (List.map (find_readback_of (module B) current_mutrec_block) params)
  | t -> [%expr [%e conversion_of (module B) t ].Elpi.API.ContextualConversion.readback ]
  in
    aux ty

let rec find_ty_ast_of (module B : Ast_builder.S) current_mutrec_block  ty = let open B in
  match ty with
  | { ptyp_desc = Ptyp_constr ({ txt = Longident.Lident id; _ }, []); _ }
    when List.mem id current_mutrec_block ->
      [%expr Elpi.API.ContextualConversion.TyName([%e evar @@ elpi_tname_str id])]
  | { ptyp_desc = Ptyp_constr ({ txt = Longident.Lident id; _ }, p::ps); _ }
    when List.mem id current_mutrec_block ->
      [%expr Elpi.API.ContextualConversion.TyApp([%e evar @@ elpi_tname_str id],[%e find_ty_ast_of (module B) current_mutrec_block p],[%e elist @@ List.map (find_ty_ast_of (module B) current_mutrec_block) ps ])]
  | [%type: [%t? typ] list]          -> [%expr Elpi.API.ContextualConversion.TyApp("list", [%e find_ty_ast_of (module B) current_mutrec_block typ ], [])]
  | [%type: [%t? typ] option]        -> [%expr Elpi.API.ContextualConversion.TyApp("option", [%e find_ty_ast_of (module B) current_mutrec_block typ ], [])]
  | [%type: [%t? typ1] * [%t? typ2]] -> [%expr Elpi.API.ContextualConversion.TyApp("pair", [%e find_ty_ast_of (module B) current_mutrec_block typ1 ], [ [%e find_ty_ast_of (module B) current_mutrec_block typ2 ] ])]
  | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3]] -> [%expr Elpi.API.ContextualConversion.TyApp("triple",  [%e find_ty_ast_of (module B) current_mutrec_block typ1 ], [ [%e find_ty_ast_of (module B) current_mutrec_block typ2 ]; [%e find_ty_ast_of (module B) current_mutrec_block typ3 ] ])]
  | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3] * [%t? typ4]] -> [%expr Elpi.API.ContextualConversion.TyApp("quadruple", [%e find_ty_ast_of (module B) current_mutrec_block typ1 ], [ [%e find_ty_ast_of (module B) current_mutrec_block typ2 ]; [%e find_ty_ast_of (module B) current_mutrec_block typ3 ]; [%e find_ty_ast_of (module B) current_mutrec_block typ4 ]   ])]
  | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3] * [%t? typ4] * [%t? typ5]] -> [%expr Elpi.API.ContextualConversion.TyApp("quintuple", [%e find_ty_ast_of (module B) current_mutrec_block typ1 ], [ [%e find_ty_ast_of (module B) current_mutrec_block typ2 ]; [%e find_ty_ast_of (module B) current_mutrec_block typ3 ]; [%e find_ty_ast_of (module B) current_mutrec_block typ4 ]; [%e find_ty_ast_of (module B) current_mutrec_block typ5 ] ])]
  | t -> [%expr [%e conversion_of (module B) t ].Elpi.API.ContextualConversion.ty ]

let find_mapper_of (module B : Ast_builder.S) current_mutrec_block params ty = let open B in
  let rec aux ty =
    match ty with
    | [%type: [%t? typ] list]          -> [%expr Printf.sprintf "(ppx.map.list %s)" [%e aux typ] ]
    | [%type: [%t? typ] option]        -> [%expr Printf.sprintf "(ppx.map.option %s)" [%e aux typ] ]
    | [%type: [%t? typ1] * [%t? typ2]] -> [%expr Printf.sprintf "(ppx.map.pair %s %s)" [%e aux typ1] [%e aux typ2] ]
    | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3]] -> [%expr Printf.sprintf "(ppx.map.triple %s %s %s)" [%e aux typ1] [%e aux typ2] [%e aux typ3] ]
    | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3] * [%t? typ4]] -> [%expr Printf.sprintf "(ppx.map.quadruple %s %s %s %s)" [%e aux typ1] [%e aux typ2] [%e aux typ3] [%e aux typ4] ]
    | [%type: [%t? typ1] * [%t? typ2] * [%t? typ3] * [%t? typ4] * [%t? typ5]] -> [%expr Printf.sprintf "(ppx.map.quintuple  %s %s %s %s %s)" [%e aux typ1] [%e aux typ2] [%e aux typ3] [%e aux typ4] [%e aux typ5] ]
    | { ptyp_desc = Ptyp_constr ({ txt = Longident.Lident id; _ }, []); _ } when List.mem_assoc id params ->
        estring @@ List.assoc id params
    | { ptyp_desc = Ptyp_constr ({ txt = Longident.Lident id; _ }, []); _ } when List.mem id current_mutrec_block ->
        [%expr "map." ^ [%e evar @@ elpi_tname_str id]]
    | { ptyp_desc = Ptyp_constr ({ txt = Longident.Lident id; _ }, ps); _ } when List.mem id current_mutrec_block ->
        [%expr "(map." ^ [%e evar @@ elpi_tname_str id] ^ " " ^ String.concat " " [%e elist @@ List.map (aux) ps] ^ ")"]
    | _ -> [%expr "(=)"]
  in
    fun (v1,v2) -> [%expr "(" ^ [%e aux ty] ^ " " ^ [%e estring v1 ] ^ " " ^[%e estring v2 ] ^ ")" ]
;;

let one_string = function
  | { pexp_desc = Pexp_constant (Pconst_string(s,_)); _ } -> Some s
  | _ -> None

let one_or_two_strings (module B : Ast_builder.S) = function
  | Pexp_constant (Pconst_string (s,_)) -> s, None
  | Pexp_apply(x,[_,y]) when is_some (one_string x) && is_some (one_string y) ->
     option_get (one_string x), one_string y
  | _ -> error "string or ident expected"

let get_elpi_code (module B : Ast_builder.S) kname kattributes =
  match Attribute.get att_elpi_code kattributes with
  | None -> elpi_name_mangle kname, None
  | Some payload -> one_or_two_strings (module B) payload.pexp_desc

let get_elpi_tcode (module B : Ast_builder.S) kname kattributes =
  match Attribute.get att_elpi_tcode kattributes with
  | None -> elpi_name_mangle kname, None
  | Some payload -> one_or_two_strings (module B) payload.pexp_desc

let get_elpi_doc kname kattributes =
  option_default kname (Attribute.get att_elpi_doc kattributes)
let get_elpi_tdoc kname kattributes =
  option_default kname (Attribute.get att_elpi_tdoc kattributes)
let get_elpi_treadback tattributes =
  Attribute.get att_elpi_treadback tattributes
let get_elpi_pp tattributes =
  Attribute.get att_elpi_pp tattributes

let analyze_tuple_constructor (module B : Ast_builder.S) tyname kname kattributes tl constructor pattern same_mutrec_block = let open B in
    let c_str = elpi_kname_str tyname kname in
    let c = elpi_kname tyname kname in
    let elpi_doc = get_elpi_doc kname kattributes in
    let str, elpi_code = get_elpi_code (module B) kname kattributes in
    let decl_str = value_binding ~pat:(pvar c_str) ~expr:(estring str) in
    let decl = value_binding ~pat:(pvar c) ~expr:[%expr Elpi.API.RawData.Constants.declare_global_symbol [%e evar @@ c_str ] ] in
    let tl =
      tl |> List.map (fun t ->
          match Attribute.get att_elpi_binder t with
          | Some { pexp_desc = Pexp_apply({ pexp_desc = Pexp_ident { txt; _}; _},[_,arg]) ; _ } ->
              HO {
                argHO_arrow_src = String.concat "." @@ Longident.flatten_exn txt;
                argHO_build_ctx = arg;
                argHO_readback = find_readback_of (module B) same_mutrec_block t;
                argHO_embed = find_embed_of (module B) same_mutrec_block t;
                argHO_ty_ast = find_ty_ast_of (module B) same_mutrec_block t;
                argHO_ty = t;
              }
          | Some { pexp_desc = Pexp_apply({ pexp_desc = Pexp_constant (Pconst_string(txt,_)); _},[_,arg]) ; _ } ->
              HO {
                argHO_arrow_src = txt;
                argHO_build_ctx = arg;
                argHO_readback = find_readback_of (module B) same_mutrec_block t;
                argHO_embed = find_embed_of (module B) same_mutrec_block t;
                argHO_ty_ast = find_ty_ast_of (module B) same_mutrec_block t;
                argHO_ty = t;
              }
          | Some e ->
              HO{
                argHO_arrow_src = tyname;
                argHO_build_ctx = e;
                argHO_readback = find_readback_of (module B) same_mutrec_block t;
                argHO_embed = find_embed_of (module B) same_mutrec_block t;
                argHO_ty_ast = find_ty_ast_of (module B) same_mutrec_block t;
                argHO_ty = t;
             }
          | None ->
             let argFO_key = None <> Attribute.get att_elpi_key t in
             FO {
               argFO_readback = find_readback_of (module B) same_mutrec_block t;
               argFO_embed = find_embed_of (module B) same_mutrec_block t;
               argFO_key;
               argFO_ty_ast = find_ty_ast_of (module B) same_mutrec_block t;
               argFO_ty = t;
             }) in
    let readback = Attribute.get att_elpi_readback kattributes in
    let embed = Attribute.get att_elpi_embed kattributes in
    let readback, embed =
      let var_ = option_map (option_default [%expr fun x -> x]) (Attribute.get att_elpi_var kattributes) in
      let opt2custom = function None -> Standard | Some x -> Custom(x,B.loc.loc_end) in
      match readback, embed, var_ with
      | _, _, None -> opt2custom readback, opt2custom embed
      | None, None, Some p ->
          if List.length tl = 1 then Name p, Name p
          else error "[@elpi.var] on a constructor with zero or more than one argument and not [@elpi.readback]"
      | None, (Some _ as e), Some p ->
          if List.length tl = 1 then Name p, opt2custom e
          else error "[@elpi.var] on a constructor with more than one argument and not [@elpi.readback]"
      | (Some _ as r), None, Some p -> opt2custom r, Name p
      | Some _, Some _, Some _ -> error "[@elpi.var] on a constructor with [@elpi.readback] and [@elpi.embed]" in
    Expose { declaration = [pstr_value Nonrecursive [decl_str]; pstr_value Nonrecursive [decl]] ; constant = evar c; constant_name = str; elpi_code = option_map estring elpi_code; elpi_doc; types = tl; constructor; pattern; embed; readback }
;;

let analyze_constructor (module B : Ast_builder.S) tyname same_mutrec_block decl = let open B in
  match decl with
  | { pcd_name = { txt = kname ; _ }; pcd_args; _ } when Attribute.get att_elpi_skip decl = Some () ->
      Skip { constructor_name = kname; has_args = not (pcd_args = Pcstr_tuple []) }
  | { pcd_name = { txt = kname ; _ }; pcd_args = Pcstr_tuple tl; pcd_res = None; _ } ->
      let make_k args =
        if args = [] then pexp_construct (Located.lident kname) None
        else pexp_construct (Located.lident kname) (Some (pexp_tuple args)) in
      let match_k args =
        if args = [] then ppat_construct (Located.lident kname) None
        else ppat_construct (Located.lident kname) (Some (ppat_tuple args)) in
      analyze_tuple_constructor (module B) tyname kname decl tl make_k match_k same_mutrec_block
  | { pcd_name = { txt = kname ; _ }; pcd_args = Pcstr_record lbltl; pcd_res = None; _ } ->
      let lbls, tl = List.(split (map (fun { pld_name = { txt; _ }; pld_type; _} -> txt, pld_type) lbltl)) in
      let make_k args = pexp_construct (Located.lident kname) (Some (pexp_record (List.map2 (fun x y -> B.Located.lident x,y) lbls args) None)) in
      let match_k args = ppat_construct (Located.lident kname) (Some (ppat_record (List.map2 (fun x y -> B.Located.lident x,y) lbls args) Closed)) in
      analyze_tuple_constructor (module B) tyname kname decl tl make_k match_k same_mutrec_block
  | { pcd_loc = loc; _ } -> error ~loc "unsupportd constructor declaration"

let extract_tyvar (x,_) =
  match x.ptyp_desc with
  | Ptyp_var s -> s
  | _ -> error ~loc:x.ptyp_loc "Type abstracted over something that is not a type variable"

let analyze_params (module B : Ast_builder.S) params = let open B in
  let tyvars = List.map extract_tyvar params in
  let mapper = object
    inherit Ast_traverse.map as super
    method! core_type x =
      match x.ptyp_desc with
      | Ptyp_var x when List.mem x tyvars -> ptyp_constr  (B.Located.mk (Longident.parse @@ param_prefix ^ x)) []
      | _ -> super#core_type x
    end in
  List.map ((^) param_prefix) tyvars, mapper

let mk_kind (module B : Ast_builder.S) vl name = let open B in
  match List.map (fun x -> [%expr [%e evar x ].Elpi.API.ContextualConversion.ty]) vl with
  | [] -> [%expr Elpi.API.ContextualConversion.TyName [%e name ]]
  | x :: xs -> [%expr Elpi.API.ContextualConversion.TyApp([%e name], [%e x], [%e elist @@ xs])]

let consistency_check ~loc (tyd,kind) =
  let name, csts =
    match tyd with
    | { name; type_decl = Algebraic (l,_); _ } -> name, drop_skip l
    | { name; _ } -> name, [] in
  let some_have_key =
    List.exists (fun { types; _ } -> List.exists is_key types) csts in
  let some_have_under =
    List.exists (fun { types; _ } -> List.exists is_HO types) csts in
  let all_have_1_key =
    List.for_all (fun { types; _ } ->
      1 = List.(length (filter is_key types))) csts in
  let some_k_is_var =
    List.exists (function { embed = Name _; _ } | { readback = Name _; _ } -> true | _ -> false) csts in
  match kind with
  | ADT when some_have_key || some_k_is_var || some_have_under->
    error ~loc "type %s is a simple ADT but uses [@elpi.var] or [@elpi.key] or [@elpi.binder]. Use [@@elpi : type] to make it a HOADT or [@@elpi (module M)] to make it a context ADT" name
  | CTX _ when not all_have_1_key ->
    error ~loc "type %s is a context ADT but has a constructor that does not have exactly one argumet marked as [@elpi.key]" name
  | CTX _ when tyd.params <> [] ->
    error ~loc "type %s is a context ADT but has parameters, not supported" name
  | HOAS _ when not (some_k_is_var || some_have_under) ->
    error ~loc "type %s is a HOADT but has no constructor flagged as [@elpi.var] nor arguments flagged as [@elpi.binder]" name
  | _ -> ()
;;

let pp_doc (module B : Ast_builder.S) kind elpi_name elpi_code elpi_doc is_pred csts = let open B in [%expr fun fmt () ->
  [%e match elpi_code with
  | None -> [%expr Elpi.API.PPX.Doc.kind fmt [%e kind] ~doc:[%e estring elpi_doc ] ]
  | Some code ->
      [%expr
        Elpi.API.Doc.comment fmt ("% " ^ [%e estring elpi_doc ]);
        Format.fprintf fmt "@\n@[<hov2>kind %s@[<hov> %s.@]@]@\n"
          [%e elpi_name ] [%e code ] ]
  ] ;
  [%e esequence @@
      List.(concat @@ (drop_skip csts |> map (fun { constant_name = c; types; embed; readback; elpi_code; elpi_doc; _ } ->
        let types, ty =
          if is_pred then ctx_index_ty (module B) :: types, [%expr Elpi.API.ContextualConversion.TyName "prop"]
          else types, [%expr kind ] in
        if is_name embed || is_name readback then []
        else [
          match elpi_code with
          | Some code ->
              [%expr
                Format.fprintf fmt "@[<hov2>type %s@[<hov> %s. %% %s@]@]@\n" [%e estring c] [%e code] [%e estring elpi_doc ]]
          | None -> [%expr Elpi.API.PPX.Doc.constructor fmt
            ~ty:[%e ty ]
            ~name:[%e estring c]
            ~doc:[%e estring elpi_doc ]
            ~args:[%e elist @@ List.map (function
                | FO { argFO_ty_ast; _ } -> argFO_ty_ast
                | HO { argHO_arrow_src = s; argHO_ty_ast; _ } ->
                    [%expr Elpi.API.ContextualConversion.TyApp("->",
                             Elpi.API.ContextualConversion.TyName [%e estring s],
                             [[%e argHO_ty_ast]]) ]
                ) types]
          ]])))
  ]]
;;


let typeabbrev_for (module B : Ast_builder.S) f params = let open B in
  let vars = List.mapi (fun i _ -> Printf.sprintf "A%d" i) params in
  if params = [] then f else [%expr "(" ^ [%e f]  ^ " " ^ [%e estring (String.concat " " vars) ] ^")" ]

let typeabbrev_for_conv (module B : Ast_builder.S) ct = let open B in
  [%expr Elpi.API.PPX.Doc.show_ty_ast ~outer: false @@ [%e conversion_of (module B) ct].Elpi.API.ContextualConversion.ty ]

let mk_pp_name (module B : Ast_builder.S) name = function
  | None -> if name = "t" then B.evar "pp" else B.evar ("pp_" ^ name)
  | Some e -> e

let pp_for_conversion (module B : Ast_builder.S) name is_pred params pp = let open B in
  let pp = mk_pp_name (module B) name pp in
  if is_pred then [%expr fun fmt (_,x) -> [%e pp] fmt x]
  else eapply pp (List.map (fun x -> [%expr [%e evar x].pp]) params)

let quantify_ty_over_params (module B : Ast_builder.S) params t = let open B in
  ptyp_poly (List.map Located.mk params) t

let conversion_type (module B : Ast_builder.S) name params is_pred = let open B in
  let rec aux = function
    | [] ->
         let t = ptyp_constr (Located.lident name) (List.map ptyp_var params) in
         let t = if is_pred then ptyp_tuple [ [%type: Elpi.API.RawData.constant ] ;t] else t in
         [%type: ([%t t ],'elpi__param__poly_hyps,'elpi__param__poly_csts) Elpi.API.ContextualConversion.t]
    | t :: ts -> [%type: ([%t ptyp_var t ],'elpi__param__poly_hyps,'elpi__param__poly_csts) Elpi.API.ContextualConversion.t -> [%t aux ts]]
  in
    quantify_ty_over_params (module B) (params @ ["elpi__param__poly_hyps"; "elpi__param__poly_csts"]) (aux params)


let readback_type (module B : Ast_builder.S) name params is_pred = let open B in
  let rec aux = function
    | [] ->
         let t = ptyp_constr (Located.lident name) (List.map ptyp_var params) in
         let t = if is_pred then ptyp_tuple [ [%type: Elpi.API.RawData.constant ] ;t] else t in
         [%type: ([%t t ],'elpi__param__poly_hyps,'elpi__param__poly_csts) Elpi.API.ContextualConversion.readback]
    | t :: ts -> [%type: ([%t ptyp_var t ],'elpi__param__poly_hyps,'elpi__param__poly_csts) Elpi.API.ContextualConversion.readback -> [%t aux ts]]
  in
    quantify_ty_over_params (module B) (params @ ["elpi__param__poly_hyps"; "elpi__param__poly_csts"]) (aux params)

let embed_type (module B : Ast_builder.S) name params is_pred = let open B in
  let rec aux = function
    | [] ->
         let t = ptyp_constr (Located.lident name) (List.map ptyp_var params) in
         let t = if is_pred then ptyp_tuple [ [%type: Elpi.API.RawData.constant ] ;t] else t in
         [%type: ([%t t ],'elpi__param__poly_hyps,'elpi__param__poly_csts) Elpi.API.ContextualConversion.embedding]
    | t :: ts -> [%type: ([%t ptyp_var t ],'elpi__param__poly_hyps,'elpi__param__poly_csts) Elpi.API.ContextualConversion.embedding -> [%t aux ts]]
  in
    quantify_ty_over_params (module B) (params @ ["elpi__param__poly_hyps"; "elpi__param__poly_csts"]) (aux params)


let coversion_for_opaque (module B : Ast_builder.S) elpi_name name pp = let open B in
  value_binding ~pat:(ppat_constraint (pvar name) [%type: [%t ptyp_constr (Located.lident name) []] Elpi.API.Conversion.t]) ~expr:[%expr
      Elpi.API.OpaqueData.declare {
        Elpi.API.OpaqueData.name = [%e elpi_name ] ;
        doc = "";
        pp = ([%e mk_pp_name (module B) name pp ]);
        compare = Pervasives.compare;
        hash = Hashtbl.hash;
        hconsed = false;
        constants = [];
      }
  ]

let conversion_for_alias (module B : Ast_builder.S) orig name params _same_mutrec_block = let open B in
  let conv = conversion_of (module B) orig in
  value_binding ~pat:(ppat_constraint (pvar name) (conversion_type (module B) name params false)) ~expr:(abstract_expr_over_params (module B) params (fun x -> x) conv)

let conversion_for_tyd (module B : Ast_builder.S) is_pred _same_mutrec_block { name; params;  elpi_name; elpi_code; elpi_doc; type_decl; pp } = let open B in
  match type_decl with
  | Opaque -> coversion_for_opaque (module B) (estring elpi_name) name pp
  | Alias _ ->
    value_binding ~pat:(ppat_constraint (pvar name) (conversion_type (module B) name params is_pred)) ~expr:(abstract_expr_over_params (module B) params (fun x -> x) ([%expr
      let kind = [%e mk_kind (module B) params (estring elpi_name) ] in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc = [%e pp_doc (module B) [%expr kind] (estring elpi_name) (option_map estring elpi_code) elpi_doc is_pred [] ];
        pp = [%e pp_for_conversion (module B) name is_pred params pp ];
        embed = [%e eapply (evar (elpi_embed_name name)) (List.map (fun x -> [%expr [%e evar x].Elpi.API.ContextualConversion.embed]) params) ];
        readback = [%e eapply (evar (elpi_readback_name name)) (List.map (fun x -> [%expr [%e evar x].Elpi.API.ContextualConversion.readback]) params) ];
      }]))
  | Algebraic(csts,_)->
    value_binding ~pat:(ppat_constraint (pvar name) (conversion_type (module B) name params is_pred)) ~expr:(abstract_expr_over_params (module B) params (fun x -> x) ([%expr
      let kind = [%e mk_kind (module B) params (estring elpi_name) ] in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc = [%e pp_doc (module B) [%expr kind] (estring elpi_name) (option_map estring elpi_code) elpi_doc is_pred csts ];
        pp = [%e pp_for_conversion (module B) name is_pred params pp ];
        embed = [%e eapply (evar (elpi_embed_name name)) (List.map (fun x -> [%expr [%e evar x].Elpi.API.ContextualConversion.embed]) params) ];
        readback = [%e eapply (evar (elpi_readback_name name)) (List.map (fun x -> [%expr [%e evar x].Elpi.API.ContextualConversion.readback]) params) ];
      }]))
;;

let embed_for_tyd (module B : Ast_builder.S) (is_pred,ctx) same_mutrec_block { name; params; type_decl; _ } = let open B in
  match type_decl with
  | Opaque -> if params <> [] then error ~loc "opaque data type with parameters not supported";
      value_binding ~pat:(pvar (elpi_embed_name name)) ~expr:[%expr fun ~depth _ _ s t -> [%e evar name].Elpi.API.Conversion.embed ~depth s t ]
  | Alias orig ->
      value_binding ~pat:(ppat_constraint (pvar (elpi_embed_name name)) (embed_type (module B) name params is_pred))
        ~expr:(abstract_expr_over_params (module B) params elpi_embed_name @@ [%expr fun ~depth h c s t -> [%e find_embed_of (module B) same_mutrec_block orig] ~depth h c s t])
  | Algebraic(csts,_) ->
      value_binding ~pat:(ppat_constraint (pvar (elpi_embed_name name)) (embed_type (module B) name params is_pred))
        ~expr:(abstract_expr_over_params (module B) params elpi_embed_name @@ embed (module B) name (is_pred,ctx) csts)

let readback_for_tyd (module B : Ast_builder.S) (is_pred,ctx) same_mutrec_block { name; params; type_decl; _ } = let open B in
  match type_decl with
  | Opaque ->  if params <> [] then error ~loc "opaque data type with parameters not supported";
      value_binding ~pat:(pvar (elpi_readback_name name)) ~expr:[%expr fun ~depth _ _ s t -> [%e evar name].Elpi.API.Conversion.readback ~depth s t ]
  | Alias orig ->
      value_binding ~pat:(ppat_constraint (pvar (elpi_readback_name name)) (readback_type (module B) name params is_pred))
        ~expr:(abstract_expr_over_params (module B) params elpi_readback_name @@ [%expr fun ~depth h c s t -> [%e find_readback_of (module B) same_mutrec_block orig] ~depth h c s t])
  | Algebraic(csts,def_readback) ->
      value_binding ~pat:(ppat_constraint (pvar (elpi_readback_name name)) (readback_type (module B) name params is_pred))
        ~expr:(abstract_expr_over_params (module B) params elpi_readback_name @@ readback (module B) name (is_pred,ctx) def_readback csts)

let constants_of_tyd (module B : Ast_builder.S) { type_decl ; elpi_name; name; _ } = let open B in
  let c_str = elpi_tname_str name in
  let decl_str =
    value_binding ~pat:(pvar c_str) ~expr:(estring elpi_name) in
  let decl =
    let c = elpi_tname name in
    value_binding ~pat:(pvar c) ~expr:[%expr Elpi.API.RawData.Constants.declare_global_symbol [%e evar c_str ]] in
  pstr_value Nonrecursive [decl_str] ::
  pstr_value Nonrecursive [decl] ::
  match type_decl with
  | Alias _ -> []
  | Opaque -> []
  | Algebraic (csts,_) -> List.flatten @@ List.map (fun x -> x.declaration) @@ drop_skip csts

let elpi_declaration_of_tyd (module B : Ast_builder.S) tyd = let open B in
  let decl_name = "elpi_"^tyd.name in
  let decl =
    match tyd.type_decl with
    | Alias orig ->
      (if tyd.params = [] then (fun x -> x)
       else pexp_let Nonrecursive (List.mapi (fun i x -> value_binding ~pat:(pvar x) ~expr:[%expr Elpi.API.ContextualConversion.(!>) @@ Elpi.API.BuiltInData.poly (Printf.sprintf "A%d" [%e eint i]) ]) tyd.params))
      [%expr
        Elpi.API.BuiltIn.LPCode ("typeabbrev " ^
          [%e typeabbrev_for (module B) (estring tyd.elpi_name) tyd.params ] ^ " " ^
          [%e typeabbrev_for_conv (module B) orig ] ^ ". % " ^ [%e estring tyd.elpi_doc ]) ]
    | Opaque ->
          [%expr Elpi.API.BuiltIn.MLData [%e
              if tyd.params = [] then evar tyd.name
              else error ~loc "opaque with params" ]]
    | Algebraic _ ->
      let vars = List.mapi (fun i _ -> [%expr Elpi.API.ContextualConversion.(!>) @@ Elpi.API.BuiltInData.poly [%e estring @@ Printf.sprintf "A%d" i] ]) tyd.params in
      [%expr Elpi.API.BuiltIn.MLDataC [%e
              if tyd.params = [] then evar tyd.name
              else eapply (evar tyd.name) vars]] in
  { decl = pstr_value Nonrecursive [value_binding ~pat:(pvar decl_name) ~expr:decl];
    decl_name = evar decl_name; }

let mapper_for_tyd (module B : Ast_builder.S) is_pred same_block tyd = let open B in
  if is_pred then None else
  let tyvars = List.mapi (fun i _ -> Printf.sprintf "X%d" i) tyd.params in
  let tyvars1 = List.mapi (fun i _ -> Printf.sprintf "Y%d" i) tyd.params in
  let ty_w_params vars =
    if vars = [] then tyd.elpi_name
    else tyd.elpi_name ^ " " ^ String.concat " " vars in
  let fvars = List.mapi (fun i _ -> Printf.sprintf "F%d" i) tyd.params in
  let param2fv = List.combine tyd.params fvars in
  let ty_fvars =
    if tyvars = [] then ""
    else String.concat ", " (List.map2 (Printf.sprintf "i:(%s -> %s -> prop)") tyvars tyvars1) ^ ", " in
  let pred_decl =
    estring @@ Printf.sprintf "pred map.%s %s i:%s, o:%s." tyd.elpi_name ty_fvars (ty_w_params tyvars) (ty_w_params tyvars1) in
  let fvars_str = if fvars = [] then "" else (String.concat " " fvars ^ " ") in
  match tyd.type_decl with
  | Opaque -> None
  | Alias orig ->
      let mapper =
        [%expr Printf.sprintf "map.%s %sA B :- %s."
          [%e estring @@ tyd.elpi_name]
          [%e estring @@ fvars_str]
          [%e find_mapper_of (module B) same_block param2fv orig ("A","B") ]] in
      Some [%expr String.concat "\n" [%e elist [pred_decl ; mapper]]]
  | Algebraic(csts,_) ->
      let mapka ty (v1,v2) =
        match ty with
        | FO { argFO_ty; _ } -> find_mapper_of (module B) same_block param2fv argFO_ty (v1,v2)
        | HO _ -> [%expr Printf.sprintf "(pi x\ fixme x => (=) %s %s)" [%e estring @@ v1] [%e estring @@ v2] ] in
      let mapk { constant_name; types; _ } =
        if types = [] then
          estring @@ Printf.sprintf "map.%s %s%s %s." tyd.elpi_name fvars_str constant_name constant_name
        else
          let vars = List.mapi (fun i _ -> Printf.sprintf "A%d" i) types in
          let vars1 = List.mapi (fun i _ -> Printf.sprintf "B%d" i) types in
          let vars_s = String.concat " " vars in
          let vars1_s = String.concat " " vars1 in
          let body = List.map2 mapka types (List.combine vars vars1) in
          [%expr Printf.sprintf "map.%s %s(%s %s) (%s %s) :- %s."
              [%e estring @@ tyd.elpi_name]
              [%e estring @@ fvars_str]
              [%e estring @@ constant_name]
              [%e estring @@ vars_s]
              [%e estring @@ constant_name]
              [%e estring @@ vars1_s]
              (String.concat ", " [%e elist @@ body])] in
      let mapper = List.map mapk (drop_skip csts) in
      Some [%expr String.concat "\n" [%e elist @@ (pred_decl :: mapper @ [estring "\n"])]]

let extras_of_task (module B : Ast_builder.S) (tyd,kind) same_mutrec_block = let open B in
  match kind with
  | ADT -> {
      ty_constants = constants_of_tyd (module B) tyd;
      ty_embed = embed_for_tyd (module B) (false,None) same_mutrec_block tyd;
      ty_readback = readback_for_tyd (module B) (false,None) same_mutrec_block tyd;
      ty_conversion = conversion_for_tyd (module B) false same_mutrec_block tyd;
      ty_conversion_name = tyd.name;
      ty_context_helpers = [];
      ty_context_readback = [];
      ty_elpi_declaration = elpi_declaration_of_tyd (module B) tyd;
      ty_opaque = tyd.type_decl = Opaque;
      ty_library = mapper_for_tyd (module B) false same_mutrec_block tyd;
    }

  | HOAS ctx -> {
      ty_constants = constants_of_tyd (module B) tyd;
      ty_embed = embed_for_tyd (module B) (false,Some ctx) same_mutrec_block tyd;
      ty_readback = readback_for_tyd (module B) (false,Some ctx) same_mutrec_block tyd;

      ty_conversion = conversion_for_tyd (module B) false same_mutrec_block tyd;
      ty_conversion_name = tyd.name;
      ty_context_helpers = [];
      ty_context_readback = [];
      ty_elpi_declaration = elpi_declaration_of_tyd (module B) tyd;
      ty_opaque = tyd.type_decl = Opaque;
      ty_library = mapper_for_tyd (module B) false same_mutrec_block tyd;
  }

  | CTX (m,deps) ->
      let name = tyd.name in
      let elpi_Map = elpi_Map ~loc name in
      let elpi_name = tyd.elpi_name in
      let csts = match tyd.type_decl with Algebraic(x,_) -> x | _ -> error "context ADT must be explicit" in
      {
      ty_constants = constants_of_tyd (module B) tyd;
      ty_embed = embed_for_tyd (module B) (true,None) same_mutrec_block tyd;
      ty_readback = readback_for_tyd (module B) (true,None) same_mutrec_block tyd;
      ty_conversion = conversion_for_tyd (module B) true same_mutrec_block tyd;
      ty_conversion_name = tyd.name;
      ty_context_helpers = [
          pstr_module (module_binding ~name:(Located.mk (elpi_map_name name))
            ~expr:(pmod_apply (pmod_ident (Located.mk (Longident.parse "Elpi.API.Utils.Map.Make"))) m));
          pstr_value Nonrecursive [value_binding ~pat:(pvar (elpi_state_name name)) ~expr:[%expr
            Elpi.API.State.declare ~name:[%e estring elpi_name] ~pp:(fun fmt _ -> Format.fprintf fmt "TODO")
              ~init:(fun () ->
                ([%e elpi_Map "empty" ] :
                  [%t ptyp_constr (Located.lident (elpi_map_name name ^ ".t")) [ [%type: Elpi.API.RawData.constant] ] ]),
                (Elpi.API.RawData.Constants.Map.empty : [%t ptyp_constr (Located.lident name) [] ] Elpi.API.ContextualConversion.ctx_entry Elpi.API.RawData.Constants.Map.t))
          ]];
          pstr_value Nonrecursive [value_binding ~pat:(pvar (elpi_to_key name)) ~expr:(ctx_entry_key (module B) csts)];
          pstr_value Nonrecursive [value_binding ~pat:(pvar (elpi_is_ctx_entry_name name)) ~expr:(is_ctx_entry (module B) csts)];
          pstr_value Nonrecursive [value_binding ~pat:(pvar (elpi_push name)) ~expr:(ctx_push (module B) name)];
          pstr_value Nonrecursive [value_binding ~pat:(pvar (elpi_pop name)) ~expr:(ctx_pop (module B) name)];
      ];
      ty_context_readback = [
        pstr_value Nonrecursive [value_binding ~pat:(pvar (elpi_in_name_alone name)) ~expr:(ctx_readback (module B) name)];
        pstr_value Nonrecursive [value_binding ~pat:(pvar (elpi_in_name name)) ~expr:(
          compose_ctx_readback (module B) (deps @ [name])
        )]
      ];
      ty_elpi_declaration = elpi_declaration_of_tyd (module B) tyd;
      ty_opaque = tyd.type_decl = Opaque;
      ty_library = mapper_for_tyd (module B) true same_mutrec_block tyd;
    }
;;

let analyze_typedecl (module B : Ast_builder.S) same_mutrec_block tdecl =
  match tdecl with
  | {
    ptype_name = { txt = name ; _ };
    ptype_params = params;
    ptype_cstrs = [];
    ptype_kind = Ptype_abstract;
    ptype_manifest = None;
    _
    } ->
      let params, _ = analyze_params (module B) params in
      let elpi_name, elpi_code = get_elpi_tcode (module B) name tdecl in
      let elpi_doc = get_elpi_tdoc name tdecl in
      let pp = get_elpi_pp tdecl in
      { name; params; type_decl = Opaque; elpi_name; elpi_code; elpi_doc; pp }

  | {
    ptype_name = { txt = name ; _ };
    ptype_params = params;
    ptype_cstrs = [];
    ptype_kind = Ptype_abstract;
    ptype_manifest = Some alias;
    _
    } ->
      let params, typ = analyze_params (module B) params in
      let alias = typ#core_type alias in
      let elpi_name, elpi_code = get_elpi_tcode (module B) name tdecl in
      let elpi_doc = get_elpi_tdoc name tdecl in
      let pp = get_elpi_pp tdecl in
      { name; params; type_decl = Alias alias; elpi_name; elpi_code; elpi_doc; pp }

  | {
    ptype_name = { txt = name ; _ };
    ptype_params = params;
    ptype_cstrs = [];
    ptype_kind = Ptype_variant csts;
    _
    } ->
      let params, typ = analyze_params (module B) params in
      let csts = List.map typ#constructor_declaration csts in
      let csts = List.map (analyze_constructor (module B) name same_mutrec_block) csts in
      let elpi_name, elpi_code = get_elpi_tcode (module B) name tdecl in
      let elpi_doc = get_elpi_tdoc name tdecl in
      let default_readback = get_elpi_treadback tdecl in
      let pp = get_elpi_pp tdecl in
      { name; params; type_decl = Algebraic(csts,default_readback); elpi_name; elpi_code; elpi_doc; pp }

  | {
    ptype_name = { txt = name ; _ };
    ptype_params = params;
    ptype_cstrs = [];
    ptype_kind = Ptype_record lbltl;
    ptype_attributes;
    _
    } ->
      let params, typ = analyze_params (module B) params in
      let lbltl = List.map typ#label_declaration lbltl in
      let lbls, tl = List.(split (map (fun { pld_name = { txt; _ }; pld_type; _} -> txt, pld_type) lbltl)) in
      let make_k args = B.pexp_record (List.map2 (fun x y -> B.Located.lident x, y) lbls args) None in
      let match_k args = B.ppat_record (List.map2 (fun x y -> B.Located.lident x, y) lbls args) Closed in
      let kdecl = {
        pcd_name = B.Located.mk name;
        pcd_args = Pcstr_tuple [];
        pcd_res  = None;
        pcd_loc = B.loc;
        pcd_attributes = ptype_attributes;
        } in
      let csts = [analyze_tuple_constructor (module B) name name kdecl tl make_k match_k same_mutrec_block] in
      let elpi_name, elpi_code = get_elpi_tcode (module B) name tdecl in
      let elpi_doc = get_elpi_tdoc name tdecl in
      let default_readback = get_elpi_treadback tdecl in
      let pp = get_elpi_pp tdecl in
      { name; params; type_decl = Algebraic(csts,default_readback); elpi_name; elpi_code; elpi_doc; pp }

  | _ -> error ~loc:B.loc "unsupportd type declaration"
;;

let typedecl_extras index context (module B : Ast_builder.S) tyd_names tyd =
  let open B in
  let tyd = analyze_typedecl (module B) tyd_names tyd in
  let one_ty t =
    match t.ptyp_desc with
    | Ptyp_constr({ txt; _ },args) ->
        if args <> [] then nYI ~loc ~__LOC__ ()
        else
          if List.length (Longident.flatten_exn txt) > 1 then nYI ~loc ~__LOC__ ()
          else String.concat "." (Longident.flatten_exn txt)
    | _ -> error ~loc "[elpi.context] payload is invalid: %a" Ocaml_common.Pprintast.core_type (Selected_ast.To_ocaml.copy_core_type t) in
  let one_arrow t =
    match t.ptyp_desc with
    | Ptyp_arrow(_,s,t) -> one_ty s , one_ty t
    | _ -> error ~loc "[elpi.context] payload is invalid: %a" Ocaml_common.Pprintast.core_type (Selected_ast.To_ocaml.copy_core_type t) in
  let kind =
    match index, context with
    | None, None -> ADT
    | Some m, None -> CTX(m,[])
    | Some m, Some ty -> CTX(m,[one_ty ty])
    | None, Some ty ->
        match ty.ptyp_desc with
        | Ptyp_tuple l -> HOAS (List.map one_arrow l)
        | Ptyp_arrow _ -> HOAS [one_arrow ty]
        | _ -> HOAS [tyd.name, one_ty ty]
    in
  let task = tyd, kind in

  consistency_check ~loc:B.loc task;

  extras_of_task (module B) task tyd_names
;;

let tydecls ~loc index context append _r tdls =
  let module B = Ast_builder.Make(struct  let loc = loc end) in
  let open B in
  let extra = List.map (typedecl_extras index context (module B) (List.map (fun x -> x.ptype_name.txt) tdls)) tdls in
  let opaque_extra, non_opaque_extra = List.partition (fun x -> x.ty_opaque) extra in

  pstr_attribute { attr_name = Located.mk "warning"; attr_payload = PStr [pstr_eval (estring "-26-27-32-39-60") []]; attr_loc = loc } ::

  List.(concat (map (fun x -> x.ty_constants) extra)) @
  List.(concat (map (fun x -> x.ty_context_helpers) extra)) @

  begin if opaque_extra <> [] then
    List.(map (fun x -> pstr_value Nonrecursive [x.ty_conversion]) opaque_extra) @
    [pstr_value Nonrecursive List.(map (fun x -> x.ty_embed) opaque_extra)] @
    [pstr_value Nonrecursive List.(map (fun x -> x.ty_readback) opaque_extra)]
  else [] end @

  begin if non_opaque_extra <> [] then
    [pstr_value Recursive List.(map (fun x -> x.ty_embed) non_opaque_extra)] @
    [pstr_value Recursive List.(map (fun x -> x.ty_readback) non_opaque_extra)] @
    List.(map (fun x -> pstr_value Nonrecursive [x.ty_conversion]) non_opaque_extra)
  else [] end @

  List.(concat (map (fun x -> x.ty_context_readback) extra)) @
  List.(map (fun x -> x.ty_elpi_declaration.decl) extra) @
  match append with
  | None -> []
  | Some l -> [pstr_value Nonrecursive [value_binding ~pat:(punit)
      ~expr:[%expr [%e l] := ![%e l] @
               [%e elist @@ List.(map (fun x -> x.ty_elpi_declaration.decl_name) extra) ]
               @
               [%e elist @@ List.concat (List.map (fun x ->
                      match x.ty_library with
                      | None -> []
                      | Some e -> [[%expr Elpi.API.BuiltIn.LPCode [%e e]]]) extra)]
              ]]]
;;

let conversion_of_expansion ~loc ~path:_ ty =
  conversion_of (module Ast_builder.Make(struct  let loc = loc end)) ty

let conversion_extension =
  Extension.declare
    "elpi"
    Extension.Context.expression
    Ast_pattern.(ptyp __)
    conversion_of_expansion

let expand_str ~loc ~path:_ (r,tydecl) (index : module_expr option) (context : core_type option) (append : expression option) = tydecls ~loc index context append r tydecl
let expand_sig ~loc ~path:_ (_r,_tydecl) (_index : module_expr option) (_context : core_type option) = nYI ~loc ~__LOC__ ()

let attributes = Attribute.([
  T att_elpi_tcode;
  T att_elpi_tdoc;
  T att_elpi_var ;
  T att_elpi_skip ;
  T att_elpi_embed;
  T att_elpi_readback;
  T att_elpi_code;
  T att_elpi_doc;
  T att_elpi_key;
  T att_elpi_binder
])


let str_type_decl_generator =
  Deriving.Generator.make
    ~attributes
    arguments
    expand_str

let pexp_ignore = Deriving.Args.of_func (fun _ _ (_e : expression) b -> b)

let arguments = Deriving.Args.(empty
  +> arg "index" (pexp_pack __)
  +> arg "context" (pexp_constraint pexp_ignore __)
)

let sig_type_decl_generator =
  Deriving.Generator.make
    ~attributes
    arguments
    expand_sig

let my_deriver =
  Deriving.add
    ~str_type_decl:str_type_decl_generator
    ~sig_type_decl:sig_type_decl_generator
    "elpi"

let () =
  Driver.register_transformation
    ~extensions:[ conversion_extension; ]
    "elpi.conversion"