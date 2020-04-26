let declaration = ref []
module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show x = x
  end
let pp_tctx _ _ = ()
type tctx =
  | TDecl of ((string)[@elpi.key ]) * bool [@@elpi.index (module String)]
[@@deriving elpi { declaration }]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_tctx = "tctx"
    let elpi_constant_type_tctxc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_tctx
    let elpi_constant_constructor_tctx_TDecl = "tdecl"
    let elpi_constant_constructor_tctx_TDeclc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tctx_TDecl
    module Elpi_tctx_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_tctx_state =
      Elpi.API.State.declare ~name:"tctx"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_tctx_Map.empty : Elpi.API.RawData.constant
                                           Elpi_tctx_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : tctx
                                                             Elpi.API.Conversion.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
    let elpi_tctx_to_key ~depth:_  =
      function | TDecl (elpi__16, _) -> elpi__16
    let elpi_is_tctx { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x } =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_tctx_TDeclc)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Utils.type_error
                   "context entry applied to a non nominal")
          else None
      | _ -> None
    let elpi_push_tctx ~depth:elpi__depth  elpi__state elpi__name
      elpi__ctx_item =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_tctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_tctx_Map.add elpi__name elpi__i elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item
          elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_tctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    let elpi_pop_tctx ~depth:elpi__depth  elpi__state elpi__name =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_tctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_tctx_Map.remove elpi__name elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_tctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    module Ctx_for_tctx =
      struct class type t = object inherit Elpi.API.Conversion.ctx end end
    let rec elpi_embed_tctx :
      'c .
        ((Elpi.API.RawData.constant * tctx), #Ctx_for_tctx.t as 'c)
          Elpi.API.Conversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | (elpi__9, TDecl (elpi__7, elpi__8)) ->
                  let (elpi__state, elpi__13, elpi__10) =
                    Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.embed
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__9 in
                  let (elpi__state, elpi__14, elpi__11) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__7 in
                  let (elpi__state, elpi__15, elpi__12) =
                    Elpi.Builtin.PPX.embed_bool ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__8 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_tctx_TDeclc
                       [elpi__13; elpi__14; elpi__15]),
                    (List.concat [elpi__10; elpi__11; elpi__12]))
    let rec elpi_readback_tctx :
      'c .
        ((Elpi.API.RawData.constant * tctx), #Ctx_for_tctx.t as 'c)
          Elpi.API.Conversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_tctx_TDeclc ->
                    let (elpi__state, elpi__6, elpi__5) =
                      Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.readback
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__1::elpi__2::[] ->
                         let (elpi__state, elpi__1, elpi__3) =
                           Elpi.API.PPX.readback_string ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__1 in
                         let (elpi__state, elpi__2, elpi__4) =
                           Elpi.Builtin.PPX.readback_bool ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__2 in
                         (elpi__state, (elpi__6, (TDecl (elpi__1, elpi__2))),
                           (List.concat [elpi__5; elpi__3; elpi__4]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_tctx_TDeclc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "tctx" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    let tctx :
      'c .
        ((Elpi.API.RawData.constant * tctx), #Ctx_for_tctx.t as 'c)
          Elpi.API.Conversion.t
      =
      let kind = Elpi.API.Conversion.TyName "tctx" in
      {
        Elpi.API.Conversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"tctx";
               Elpi.API.PPX.Doc.constructor fmt
                 ~ty:(Elpi.API.Conversion.TyName "prop") ~name:"tdecl"
                 ~doc:"TDecl"
                 ~args:[Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.ty;
                       Elpi.API.BuiltInData.string.Elpi.API.Conversion.ty;
                       Elpi.Builtin.bool.Elpi.API.Conversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_tctx fmt x);
        embed = elpi_embed_tctx;
        readback = elpi_readback_tctx
      }
    let context_made_of_tctx =
      {
        Elpi.API.Conversion.is_entry_for_nominal = elpi_is_tctx;
        to_key = elpi_tctx_to_key;
        push = elpi_push_tctx;
        pop = elpi_pop_tctx;
        conv = tctx;
        init =
          (fun state ->
             Elpi.API.State.set elpi_tctx_state state
               ((Elpi_tctx_Map.empty : Elpi.API.RawData.constant
                                         Elpi_tctx_Map.t),
                 (Elpi.API.RawData.Constants.Map.empty : tctx
                                                           Elpi.API.Conversion.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get =
          (fun state -> snd @@ (Elpi.API.State.get elpi_tctx_state state))
      }
    let elpi_tctx = Elpi.API.BuiltIn.MLData tctx
    class ctx_for_tctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tctx.t =
      object (_) inherit  ((Elpi.API.Conversion.ctx) h) end
    let (in_ctx_for_tctx : Ctx_for_tctx.t Elpi.API.Conversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_tctx) h s), (List.concat []))
    let () = declaration := ((!declaration) @ [elpi_tctx])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let pp_tye _ _ = ()
type tye =
  | TVar of string [@elpi.var tctx]
  | TConst of string 
  | TArrow of tye * tye [@@deriving elpi { declaration }]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_tye = "tye"
    let elpi_constant_type_tyec =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_tye
    let elpi_constant_constructor_tye_TVar = "tvar"
    let elpi_constant_constructor_tye_TVarc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tye_TVar
    let elpi_constant_constructor_tye_TConst = "tconst"
    let elpi_constant_constructor_tye_TConstc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tye_TConst
    let elpi_constant_constructor_tye_TArrow = "tarrow"
    let elpi_constant_constructor_tye_TArrowc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tye_TArrow
    module Ctx_for_tye =
      struct
        class type t =
          object
            inherit Elpi.API.Conversion.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi.API.Conversion.ctx_field
          end
      end
    let rec elpi_embed_tye :
      'c . (tye, #Ctx_for_tye.t as 'c) Elpi.API.Conversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | TVar elpi__25 ->
                  let (elpi__ctx2dbl, _) =
                    Elpi.API.State.get elpi_tctx_state elpi__state in
                  let elpi__key = (fun x -> x) elpi__25 in
                  (if not (Elpi_tctx_Map.mem elpi__key elpi__ctx2dbl)
                   then Elpi.API.Utils.error "Unbound variable";
                   (elpi__state,
                     (Elpi.API.RawData.mkBound
                        (Elpi_tctx_Map.find elpi__key elpi__ctx2dbl)), []))
              | TConst elpi__28 ->
                  let (elpi__state, elpi__30, elpi__29) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__28 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_tye_TConstc [elpi__30]),
                    (List.concat [elpi__29]))
              | TArrow (elpi__31, elpi__32) ->
                  let (elpi__state, elpi__35, elpi__33) =
                    elpi_embed_tye ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__31 in
                  let (elpi__state, elpi__36, elpi__34) =
                    elpi_embed_tye ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__32 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_tye_TArrowc
                       [elpi__35; elpi__36]),
                    (List.concat [elpi__33; elpi__34]))
    let rec elpi_readback_tye :
      'c . (tye, #Ctx_for_tye.t as 'c) Elpi.API.Conversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.Const elpi__hd when elpi__hd >= 0 ->
                    let (_, elpi__dbl2ctx) =
                      Elpi.API.State.get elpi_tctx_state elpi__state in
                    (if
                       not
                         (Elpi.API.RawData.Constants.Map.mem elpi__hd
                            elpi__dbl2ctx)
                     then
                       Elpi.API.Utils.error
                         (Format.asprintf "Unbound variable: %s in %a"
                            (Elpi.API.RawData.Constants.show elpi__hd)
                            (Elpi.API.RawData.Constants.Map.pp
                               (Elpi.API.Conversion.pp_ctx_entry pp_tctx))
                            elpi__dbl2ctx);
                     (let { Elpi.API.Conversion.entry = elpi__entry;
                            depth = elpi__depth }
                        =
                        Elpi.API.RawData.Constants.Map.find elpi__hd
                          elpi__dbl2ctx in
                      (elpi__state,
                        (TVar
                           (elpi_tctx_to_key ~depth:elpi__depth elpi__entry)),
                        [])))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_tye_TConstc ->
                    let (elpi__state, elpi__20, elpi__19) =
                      Elpi.API.PPX.readback_string ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | [] ->
                         (elpi__state, (TConst elpi__20),
                           (List.concat [elpi__19]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_tye_TConstc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_tye_TArrowc ->
                    let (elpi__state, elpi__24, elpi__23) =
                      elpi_readback_tye ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__21::[] ->
                         let (elpi__state, elpi__21, elpi__22) =
                           elpi_readback_tye ~depth:elpi__depth elpi__hyps
                             elpi__constraints elpi__state elpi__21 in
                         (elpi__state, (TArrow (elpi__24, elpi__21)),
                           (List.concat [elpi__23; elpi__22]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_tye_TArrowc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "tye" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    let tye : 'c . (tye, #Ctx_for_tye.t as 'c) Elpi.API.Conversion.t =
      let kind = Elpi.API.Conversion.TyName "tye" in
      {
        Elpi.API.Conversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"tye";
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tconst"
                 ~doc:"TConst"
                 ~args:[Elpi.API.BuiltInData.string.Elpi.API.Conversion.ty];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tarrow"
                 ~doc:"TArrow"
                 ~args:[Elpi.API.Conversion.TyName elpi_constant_type_tye;
                       Elpi.API.Conversion.TyName elpi_constant_type_tye]);
        pp = pp_tye;
        embed = elpi_embed_tye;
        readback = elpi_readback_tye
      }
    let elpi_tye = Elpi.API.BuiltIn.MLData tye
    class ctx_for_tye (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tye.t =
      object (_)
        inherit  ((Elpi.API.Conversion.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx = context_made_of_tctx.Elpi.API.Conversion.get s
      end
    let (in_ctx_for_tye : Ctx_for_tye.t Elpi.API.Conversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_tctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tctx ctx
                  h c s in
              (s, ((new ctx_for_tye) h s), (List.concat [gls0]))
    let () = declaration := ((!declaration) @ [elpi_tye])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let tye : 'a . (tye, #ctx_for_tye as 'a) Elpi.API.Conversion.t = tye
let pp_ty _ _ = ()
type ty =
  | Mono of tye 
  | Forall of string * bool *
  ((ty)[@elpi.binder "tye" tctx (fun s -> fun b -> TDecl (s, b))]) [@@deriving
                                                                    elpi]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_ty = "ty"
    let elpi_constant_type_tyc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_ty
    let elpi_constant_constructor_ty_Mono = "mono"
    let elpi_constant_constructor_ty_Monoc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ty_Mono
    let elpi_constant_constructor_ty_Forall = "forall"
    let elpi_constant_constructor_ty_Forallc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ty_Forall
    module Ctx_for_ty =
      struct
        class type t =
          object
            inherit Elpi.API.Conversion.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi.API.Conversion.ctx_field
          end
      end
    let rec elpi_embed_ty :
      'c . (ty, #Ctx_for_ty.t as 'c) Elpi.API.Conversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | Mono elpi__45 ->
                  let (elpi__state, elpi__47, elpi__46) =
                    tye.Elpi.API.Conversion.embed ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__45 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ty_Monoc [elpi__47]),
                    (List.concat [elpi__46]))
              | Forall (elpi__48, elpi__49, elpi__50) ->
                  let (elpi__state, elpi__54, elpi__51) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__48 in
                  let (elpi__state, elpi__55, elpi__52) =
                    Elpi.Builtin.PPX.embed_bool ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__49 in
                  let elpi__ctx_entry =
                    (fun s -> fun b -> TDecl (s, b)) elpi__48 elpi__49 in
                  let elpi__ctx_key =
                    elpi_tctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                  let elpi__ctx_entry =
                    {
                      Elpi.API.Conversion.entry = elpi__ctx_entry;
                      depth = elpi__depth
                    } in
                  let elpi__state =
                    elpi_push_tctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key elpi__ctx_entry in
                  let (elpi__state, elpi__57, elpi__53) =
                    elpi_embed_ty ~depth:(elpi__depth + 1) elpi__hyps
                      elpi__constraints elpi__state elpi__50 in
                  let elpi__56 = Elpi.API.RawData.mkLam elpi__57 in
                  let elpi__state =
                    elpi_pop_tctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ty_Forallc
                       [elpi__54; elpi__55; elpi__56]),
                    (List.concat [elpi__51; elpi__52; elpi__53]))
    let rec elpi_readback_ty :
      'c . (ty, #Ctx_for_ty.t as 'c) Elpi.API.Conversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_ty_Monoc ->
                    let (elpi__state, elpi__38, elpi__37) =
                      tye.Elpi.API.Conversion.readback ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | [] ->
                         (elpi__state, (Mono elpi__38),
                           (List.concat [elpi__37]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_ty_Monoc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_ty_Forallc ->
                    let (elpi__state, elpi__44, elpi__43) =
                      Elpi.API.PPX.readback_string ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__39::elpi__40::[] ->
                         let (elpi__state, elpi__39, elpi__41) =
                           Elpi.Builtin.PPX.readback_bool ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__39 in
                         let elpi__ctx_entry =
                           (fun s -> fun b -> TDecl (s, b)) elpi__44 elpi__39 in
                         let elpi__ctx_key =
                           elpi_tctx_to_key ~depth:elpi__depth
                             elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi.API.Conversion.entry = elpi__ctx_entry;
                             depth = elpi__depth
                           } in
                         let elpi__state =
                           elpi_push_tctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key elpi__ctx_entry in
                         let (elpi__state, elpi__40, elpi__42) =
                           match Elpi.API.RawData.look ~depth:elpi__depth
                                   elpi__40
                           with
                           | Elpi.API.RawData.Lam elpi__bo ->
                               elpi_readback_ty ~depth:(elpi__depth + 1)
                                 elpi__hyps elpi__constraints elpi__state
                                 elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_tctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state,
                           (Forall (elpi__44, elpi__39, elpi__40)),
                           (List.concat [elpi__43; elpi__41; elpi__42]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_ty_Forallc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "ty" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    let ty : 'c . (ty, #Ctx_for_ty.t as 'c) Elpi.API.Conversion.t =
      let kind = Elpi.API.Conversion.TyName "ty" in
      {
        Elpi.API.Conversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"ty";
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"mono"
                 ~doc:"Mono" ~args:[tye.Elpi.API.Conversion.ty];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"forall"
                 ~doc:"Forall"
                 ~args:[Elpi.API.BuiltInData.string.Elpi.API.Conversion.ty;
                       Elpi.Builtin.bool.Elpi.API.Conversion.ty;
                       Elpi.API.Conversion.TyApp
                         ("->", (Elpi.API.Conversion.TyName "tye"),
                           [Elpi.API.Conversion.TyName elpi_constant_type_ty])]);
        pp = pp_ty;
        embed = elpi_embed_ty;
        readback = elpi_readback_ty
      }
    let elpi_ty = Elpi.API.BuiltIn.MLData ty
    class ctx_for_ty (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_ty.t =
      object (_)
        inherit  ((Elpi.API.Conversion.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx = context_made_of_tctx.Elpi.API.Conversion.get s
      end
    let (in_ctx_for_ty : Ctx_for_ty.t Elpi.API.Conversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_tctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tctx ctx
                  h c s in
              (s, ((new ctx_for_ty) h s), (List.concat [gls0]))
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let ty : 'a . (ty, #ctx_for_ty as 'a) Elpi.API.Conversion.t = ty
let pp_ctx _ _ = ()
type ctx =
  | Decl of ((string)[@elpi.key ]) * ty [@@elpi.index (module String)]
[@@deriving elpi { declaration; context = [tctx] }]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_ctx = "ctx"
    let elpi_constant_type_ctxc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_ctx
    let elpi_constant_constructor_ctx_Decl = "decl"
    let elpi_constant_constructor_ctx_Declc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ctx_Decl
    module Elpi_ctx_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_ctx_state =
      Elpi.API.State.declare ~name:"ctx"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_ctx_Map.empty : Elpi.API.RawData.constant
                                          Elpi_ctx_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : ctx
                                                             Elpi.API.Conversion.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
    let elpi_ctx_to_key ~depth:_  = function | Decl (elpi__73, _) -> elpi__73
    let elpi_is_ctx { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x } =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_ctx_Declc)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Utils.type_error
                   "context entry applied to a non nominal")
          else None
      | _ -> None
    let elpi_push_ctx ~depth:elpi__depth  elpi__state elpi__name
      elpi__ctx_item =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_ctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_ctx_Map.add elpi__name elpi__i elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item
          elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_ctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    let elpi_pop_ctx ~depth:elpi__depth  elpi__state elpi__name =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_ctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_ctx_Map.remove elpi__name elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_ctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    module Ctx_for_ctx =
      struct
        class type t =
          object
            inherit Elpi.API.Conversion.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi.API.Conversion.ctx_field
          end
      end
    let rec elpi_embed_ctx :
      'c .
        ((Elpi.API.RawData.constant * ctx), #Ctx_for_ctx.t as 'c)
          Elpi.API.Conversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | (elpi__66, Decl (elpi__64, elpi__65)) ->
                  let (elpi__state, elpi__70, elpi__67) =
                    Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.embed
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__66 in
                  let (elpi__state, elpi__71, elpi__68) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__64 in
                  let (elpi__state, elpi__72, elpi__69) =
                    ty.Elpi.API.Conversion.embed ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__65 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ctx_Declc
                       [elpi__70; elpi__71; elpi__72]),
                    (List.concat [elpi__67; elpi__68; elpi__69]))
    let rec elpi_readback_ctx :
      'c .
        ((Elpi.API.RawData.constant * ctx), #Ctx_for_ctx.t as 'c)
          Elpi.API.Conversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_ctx_Declc ->
                    let (elpi__state, elpi__63, elpi__62) =
                      Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.readback
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__58::elpi__59::[] ->
                         let (elpi__state, elpi__58, elpi__60) =
                           Elpi.API.PPX.readback_string ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__58 in
                         let (elpi__state, elpi__59, elpi__61) =
                           ty.Elpi.API.Conversion.readback ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__59 in
                         (elpi__state,
                           (elpi__63, (Decl (elpi__58, elpi__59))),
                           (List.concat [elpi__62; elpi__60; elpi__61]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_ctx_Declc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "ctx" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    let ctx :
      'c .
        ((Elpi.API.RawData.constant * ctx), #Ctx_for_ctx.t as 'c)
          Elpi.API.Conversion.t
      =
      let kind = Elpi.API.Conversion.TyName "ctx" in
      {
        Elpi.API.Conversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"ctx";
               Elpi.API.PPX.Doc.constructor fmt
                 ~ty:(Elpi.API.Conversion.TyName "prop") ~name:"decl"
                 ~doc:"Decl"
                 ~args:[Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.ty;
                       Elpi.API.BuiltInData.string.Elpi.API.Conversion.ty;
                       ty.Elpi.API.Conversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_ctx fmt x);
        embed = elpi_embed_ctx;
        readback = elpi_readback_ctx
      }
    let context_made_of_ctx =
      {
        Elpi.API.Conversion.is_entry_for_nominal = elpi_is_ctx;
        to_key = elpi_ctx_to_key;
        push = elpi_push_ctx;
        pop = elpi_pop_ctx;
        conv = ctx;
        init =
          (fun state ->
             Elpi.API.State.set elpi_ctx_state state
               ((Elpi_ctx_Map.empty : Elpi.API.RawData.constant
                                        Elpi_ctx_Map.t),
                 (Elpi.API.RawData.Constants.Map.empty : ctx
                                                           Elpi.API.Conversion.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get = (fun state -> snd @@ (Elpi.API.State.get elpi_ctx_state state))
      }
    let elpi_ctx = Elpi.API.BuiltIn.MLData ctx
    class ctx_for_ctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_ctx.t =
      object (_)
        inherit  ((Elpi.API.Conversion.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx = context_made_of_tctx.Elpi.API.Conversion.get s
      end
    let (in_ctx_for_ctx : Ctx_for_ctx.t Elpi.API.Conversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_tctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tctx ctx
                  h c s in
              (s, ((new ctx_for_ctx) h s), (List.concat [gls0]))
    let () = declaration := ((!declaration) @ [elpi_ctx])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type term =
  | Var of string [@elpi.var ctx]
  | App of term list [@elpi.code "appl"][@elpi.doc "bla bla"]
  | Lam of string * ty *
  ((term)[@elpi.binder ctx (fun s -> fun ty -> Decl (s, ty))]) 
  | Literal of int [@elpi.skip ]
  | Cast of term * ty
  [@elpi.embed
    fun default ->
      fun ~depth ->
        fun hyps ->
          fun constraints ->
            fun state ->
              fun a1 -> fun a2 -> default ~depth hyps constraints state a1 a2]
  [@elpi.readback
    fun default ->
      fun ~depth ->
        fun hyps ->
          fun constraints ->
            fun state -> fun l -> default ~depth hyps constraints state l]
  [@elpi.code "type-cast" "term -> ty -> term"][@@deriving
                                                 elpi
                                                   { context = [tctx; ctx] }]
[@@elpi.pp
  let rec aux fmt =
    function
    | Var s -> Format.fprintf fmt "%s" s
    | App tl -> Format.fprintf fmt "App %a" (Elpi.API.RawPp.list aux " ") tl
    | Lam (s, ty, t) -> Format.fprintf fmt "Lam %s (%a)" s aux t
    | Literal i -> Format.fprintf fmt "%d" i
    | Cast (t, _) -> aux fmt t in
  aux]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_term = "term"
    let elpi_constant_type_termc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_term
    let elpi_constant_constructor_term_Var = "var"
    let elpi_constant_constructor_term_Varc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Var
    let elpi_constant_constructor_term_App = "appl"
    let elpi_constant_constructor_term_Appc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_App
    let elpi_constant_constructor_term_Lam = "lam"
    let elpi_constant_constructor_term_Lamc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Lam
    let elpi_constant_constructor_term_Cast = "type-cast"
    let elpi_constant_constructor_term_Castc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Cast
    module Ctx_for_term =
      struct
        class type t =
          object
            inherit Elpi.API.Conversion.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi.API.Conversion.ctx_field
            inherit Ctx_for_ctx.t
            method  ctx : ctx Elpi.API.Conversion.ctx_field
          end
      end
    let rec elpi_embed_term :
      'c . (term, #Ctx_for_term.t as 'c) Elpi.API.Conversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | Var elpi__88 ->
                  let (elpi__ctx2dbl, _) =
                    Elpi.API.State.get elpi_ctx_state elpi__state in
                  let elpi__key = (fun x -> x) elpi__88 in
                  (if not (Elpi_ctx_Map.mem elpi__key elpi__ctx2dbl)
                   then Elpi.API.Utils.error "Unbound variable";
                   (elpi__state,
                     (Elpi.API.RawData.mkBound
                        (Elpi_ctx_Map.find elpi__key elpi__ctx2dbl)), []))
              | App elpi__91 ->
                  let (elpi__state, elpi__93, elpi__92) =
                    (Elpi.API.PPX.embed_list elpi_embed_term)
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__91 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_term_Appc [elpi__93]),
                    (List.concat [elpi__92]))
              | Lam (elpi__94, elpi__95, elpi__96) ->
                  let (elpi__state, elpi__100, elpi__97) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__94 in
                  let (elpi__state, elpi__101, elpi__98) =
                    ty.Elpi.API.Conversion.embed ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__95 in
                  let elpi__ctx_entry =
                    (fun s -> fun ty -> Decl (s, ty)) elpi__94 elpi__95 in
                  let elpi__ctx_key =
                    elpi_ctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                  let elpi__ctx_entry =
                    {
                      Elpi.API.Conversion.entry = elpi__ctx_entry;
                      depth = elpi__depth
                    } in
                  let elpi__state =
                    elpi_push_ctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key elpi__ctx_entry in
                  let (elpi__state, elpi__103, elpi__99) =
                    elpi_embed_term ~depth:(elpi__depth + 1) elpi__hyps
                      elpi__constraints elpi__state elpi__96 in
                  let elpi__102 = Elpi.API.RawData.mkLam elpi__103 in
                  let elpi__state =
                    elpi_pop_ctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_term_Lamc
                       [elpi__100; elpi__101; elpi__102]),
                    (List.concat [elpi__97; elpi__98; elpi__99]))
              | Literal _ ->
                  Elpi.API.Utils.error
                    ("constructor " ^ ("Literal" ^ " is not supported"))
              | Cast (elpi__104, elpi__105) ->
                  ((fun default ->
                      fun ~depth ->
                        fun hyps ->
                          fun constraints ->
                            fun state ->
                              fun a1 ->
                                fun a2 ->
                                  default ~depth hyps constraints state a1 a2))
                    (fun ~depth:elpi__depth ->
                       fun elpi__hyps ->
                         fun elpi__constraints ->
                           fun elpi__state ->
                             fun elpi__104 ->
                               fun elpi__105 ->
                                 let (elpi__state, elpi__108, elpi__106) =
                                   elpi_embed_term ~depth:elpi__depth
                                     elpi__hyps elpi__constraints elpi__state
                                     elpi__104 in
                                 let (elpi__state, elpi__109, elpi__107) =
                                   ty.Elpi.API.Conversion.embed
                                     ~depth:elpi__depth elpi__hyps
                                     elpi__constraints elpi__state elpi__105 in
                                 (elpi__state,
                                   (Elpi.API.RawData.mkAppL
                                      elpi_constant_constructor_term_Castc
                                      [elpi__108; elpi__109]),
                                   (List.concat [elpi__106; elpi__107])))
                    ~depth:elpi__depth elpi__hyps elpi__constraints
                    elpi__state elpi__104 elpi__105
    let rec elpi_readback_term :
      'c . (term, #Ctx_for_term.t as 'c) Elpi.API.Conversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.Const elpi__hd when elpi__hd >= 0 ->
                    let (_, elpi__dbl2ctx) =
                      Elpi.API.State.get elpi_ctx_state elpi__state in
                    (if
                       not
                         (Elpi.API.RawData.Constants.Map.mem elpi__hd
                            elpi__dbl2ctx)
                     then
                       Elpi.API.Utils.error
                         (Format.asprintf "Unbound variable: %s in %a"
                            (Elpi.API.RawData.Constants.show elpi__hd)
                            (Elpi.API.RawData.Constants.Map.pp
                               (Elpi.API.Conversion.pp_ctx_entry pp_ctx))
                            elpi__dbl2ctx);
                     (let { Elpi.API.Conversion.entry = elpi__entry;
                            depth = elpi__depth }
                        =
                        Elpi.API.RawData.Constants.Map.find elpi__hd
                          elpi__dbl2ctx in
                      (elpi__state,
                        (Var (elpi_ctx_to_key ~depth:elpi__depth elpi__entry)),
                        [])))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Appc ->
                    let (elpi__state, elpi__77, elpi__76) =
                      (Elpi.API.PPX.readback_list elpi_readback_term)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | [] ->
                         (elpi__state, (App elpi__77),
                           (List.concat [elpi__76]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Appc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Lamc ->
                    let (elpi__state, elpi__83, elpi__82) =
                      Elpi.API.PPX.readback_string ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__78::elpi__79::[] ->
                         let (elpi__state, elpi__78, elpi__80) =
                           ty.Elpi.API.Conversion.readback ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__78 in
                         let elpi__ctx_entry =
                           (fun s -> fun ty -> Decl (s, ty)) elpi__83
                             elpi__78 in
                         let elpi__ctx_key =
                           elpi_ctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi.API.Conversion.entry = elpi__ctx_entry;
                             depth = elpi__depth
                           } in
                         let elpi__state =
                           elpi_push_ctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key elpi__ctx_entry in
                         let (elpi__state, elpi__79, elpi__81) =
                           match Elpi.API.RawData.look ~depth:elpi__depth
                                   elpi__79
                           with
                           | Elpi.API.RawData.Lam elpi__bo ->
                               elpi_readback_term ~depth:(elpi__depth + 1)
                                 elpi__hyps elpi__constraints elpi__state
                                 elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_ctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state, (Lam (elpi__83, elpi__78, elpi__79)),
                           (List.concat [elpi__82; elpi__80; elpi__81]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Lamc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Castc ->
                    ((fun default ->
                        fun ~depth ->
                          fun hyps ->
                            fun constraints ->
                              fun state ->
                                fun l ->
                                  default ~depth hyps constraints state l))
                      (fun ~depth:elpi__depth ->
                         fun elpi__hyps ->
                           fun elpi__constraints ->
                             fun elpi__state ->
                               function
                               | elpi__x::elpi__xs ->
                                   let (elpi__state, elpi__87, elpi__86) =
                                     elpi_readback_term ~depth:elpi__depth
                                       elpi__hyps elpi__constraints
                                       elpi__state elpi__x in
                                   (match elpi__xs with
                                    | elpi__84::[] ->
                                        let (elpi__state, elpi__84, elpi__85)
                                          =
                                          ty.Elpi.API.Conversion.readback
                                            ~depth:elpi__depth elpi__hyps
                                            elpi__constraints elpi__state
                                            elpi__84 in
                                        (elpi__state,
                                          (Cast (elpi__87, elpi__84)),
                                          (List.concat [elpi__86; elpi__85]))
                                    | _ ->
                                        Elpi.API.Utils.type_error
                                          ("Not enough arguments to constructor: "
                                             ^
                                             (Elpi.API.RawData.Constants.show
                                                elpi_constant_constructor_term_Castc)))
                               | [] ->
                                   Elpi.API.Utils.error
                                     ~loc:{
                                            Elpi.API.Ast.Loc.source_name =
                                              "test_two_layers_context.ml";
                                            source_start = 1815;
                                            source_stop = 1815;
                                            line = 55;
                                            line_starts_at = 1804
                                          }
                                     "standard branch readback takes 1 argument or more")
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state (elpi__x :: elpi__xs)
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "term" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    let term : 'c . (term, #Ctx_for_term.t as 'c) Elpi.API.Conversion.t =
      let kind = Elpi.API.Conversion.TyName "term" in
      {
        Elpi.API.Conversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"term";
               (Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"appl"
                  ~doc:"bla bla"
                  ~args:[Elpi.API.Conversion.TyApp
                           ("list",
                             (Elpi.API.Conversion.TyName
                                elpi_constant_type_term), [])];
                Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"lam"
                  ~doc:"Lam"
                  ~args:[Elpi.API.BuiltInData.string.Elpi.API.Conversion.ty;
                        ty.Elpi.API.Conversion.ty;
                        Elpi.API.Conversion.TyApp
                          ("->", (Elpi.API.Conversion.TyName "term"),
                            [Elpi.API.Conversion.TyName
                               elpi_constant_type_term])]);
               Format.fprintf fmt "@[<hov2>type %s@[<hov> %s. %% %s@]@]@\n"
                 "type-cast" "term -> ty -> term" "Cast");
        pp =
          (let rec aux fmt =
             function
             | Var s -> Format.fprintf fmt "%s" s
             | App tl ->
                 Format.fprintf fmt "App %a" (Elpi.API.RawPp.list aux " ") tl
             | Lam (s, ty, t) -> Format.fprintf fmt "Lam %s (%a)" s aux t
             | Literal i -> Format.fprintf fmt "%d" i
             | Cast (t, _) -> aux fmt t in
           aux);
        embed = elpi_embed_term;
        readback = elpi_readback_term
      }
    let elpi_term = Elpi.API.BuiltIn.MLData term
    class ctx_for_term (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_term.t =
      object (_)
        inherit  ((Elpi.API.Conversion.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx = context_made_of_tctx.Elpi.API.Conversion.get s
        inherit ! ((ctx_for_ctx) h s)
        method ctx = context_made_of_ctx.Elpi.API.Conversion.get s
      end
    let (in_ctx_for_term : Ctx_for_term.t Elpi.API.Conversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_tctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tctx ctx
                  h c s in
              let ctx = (new ctx_for_ctx) h s in
              let (s, gls1) =
                Elpi.API.PPX.readback_context ~depth context_made_of_ctx ctx
                  h c s in
              (s, ((new ctx_for_term) h s), (List.concat [gls0; gls1]))
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let term : 'a . (term, #ctx_for_term as 'a) Elpi.API.Conversion.t = term
open Elpi.API
open BuiltInPredicate
open Notation
let term_to_string =
  Pred
    ("term->string",
      (In (term, "T", (Out (BuiltInData.string, "S", (Read "what else"))))),
      in_ctx_for_term,
      (fun (t : term) ->
         fun (_ety : string oarg) ->
           fun ~depth:_ ->
             fun c ->
               fun (_cst : Data.constraints) ->
                 fun (_state : State.t) ->
                   !:
                     (Format.asprintf "@[<hov>%a@ %a@ |-@ %a@]@\n%!"
                        (RawData.Constants.Map.pp
                           (Conversion.pp_ctx_entry pp_tctx)) c#tctx
                        (RawData.Constants.Map.pp
                           (Conversion.pp_ctx_entry pp_ctx)) c#ctx term.pp t)))
let builtin =
  let open BuiltIn in
    declare ~file_name:"test_ppx.elpi"
      ((!declaration) @
         ([MLCode (term_to_string, DocAbove);
          LPDoc "----------------- elpi ----------------"] @
            (let open Elpi.Builtin in core_builtins @ elpi_builtins)))
let program =
  {|
main :-
  pi x w y q t\
    tdecl t "alpha" tt =>
    decl y "arg" (forall "ss" tt s\ mono (tarrow (tconst "nat") s)) =>
    decl x "f" (mono (tarrow (tconst "nat") t)) =>
      print {term->string (appl [x, y, lam "zzzz" (mono t) z\ z])}.

|}
let main () =
  let (elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  let out = open_out (Sys.argv.(1)) in
  let fmt = Format.formatter_of_out_channel out in
  Setup.set_err_formatter fmt;
  Setup.set_std_formatter fmt;
  (let program =
     Parse.program_from_stream ~elpi (Ast.Loc.initial "test")
       (let open Stream in of_string program) in
   let goal = Parse.goal (Ast.Loc.initial "test") "main." in
   let program = Compile.program ~elpi ~flags:Compile.default_flags [program] in
   let goal = Compile.query program goal in
   let exe = Compile.optimize goal in
   match Execute.once exe with
   | Execute.Success _ ->
       (Format.pp_print_flush fmt (); close_out out; exit 0)
   | _ -> exit 1)
;;main ()
