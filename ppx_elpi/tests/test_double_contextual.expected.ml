let declaration = ref []
module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show = Format.asprintf "%a" pp
  end
let pp_tyctx _ _ = ()
type tyctx =
  | TEntry of ((string)[@elpi.key ]) * bool [@@elpi.index (module String)]
[@@deriving elpi { declaration }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_tyctx = "tyctx"
    let elpi_constant_type_tyctxc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_tyctx
    let elpi_constant_constructor_tyctx_TEntry = "tentry"
    let elpi_constant_constructor_tyctx_TEntryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tyctx_TEntry
    module Elpi_tyctx_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_tyctx_state =
      Elpi.API.State.declare ~name:"tyctx"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_tyctx_Map.empty : Elpi.API.RawData.constant
                                            Elpi_tyctx_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : tyctx
                                                             Elpi.API.ContextualConversion.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x)
    let elpi_tyctx_to_key ~depth:_  =
      function | TEntry (elpi__16, _) -> elpi__16
    let elpi_is_tyctx { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x }
      =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_tyctx_TEntryc)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Utils.type_error
                   "context entry applied to a non nominal")
          else None
      | _ -> None
    let elpi_push_tyctx ~depth:elpi__depth  elpi__state elpi__name
      elpi__ctx_item =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_tyctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_tyctx_Map.add elpi__name elpi__i elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item
          elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_tyctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    let elpi_pop_tyctx ~depth:elpi__depth  elpi__state elpi__name =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_tyctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_tyctx_Map.remove elpi__name elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_tyctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    module Ctx_for_tyctx =
      struct
        class type t = object inherit Elpi.API.ContextualConversion.ctx end
      end
    let rec elpi_embed_tyctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tyctx), #Ctx_for_tyctx.t as 'c, 
          'csts) Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | (elpi__9, TEntry (elpi__7, elpi__8)) ->
                  let (elpi__state, elpi__13, elpi__10) =
                    Elpi.API.BuiltInContextualData.nominal.Elpi.API.ContextualConversion.embed
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__9 in
                  let (elpi__state, elpi__14, elpi__11) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.embed
                                 ~depth h c s t) ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__7 in
                  let (elpi__state, elpi__15, elpi__12) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed
                                 ~depth h c s t) ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__8 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_tyctx_TEntryc
                       [elpi__13; elpi__14; elpi__15]),
                    (List.concat [elpi__10; elpi__11; elpi__12]))
    and elpi_readback_tyctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tyctx), #Ctx_for_tyctx.t as 'c, 
          'csts) Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_tyctx_TEntryc ->
                    let (elpi__state, elpi__6, elpi__5) =
                      Elpi.API.BuiltInContextualData.nominal.Elpi.API.ContextualConversion.readback
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__1::elpi__2::[] ->
                         let (elpi__state, elpi__1, elpi__3) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__1 in
                         let (elpi__state, elpi__2, elpi__4) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__2 in
                         (elpi__state,
                           (elpi__6, (TEntry (elpi__1, elpi__2))),
                           (List.concat [elpi__5; elpi__3; elpi__4]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_tyctx_TEntryc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "tyctx" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and tyctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tyctx), #Ctx_for_tyctx.t as 'c, 
          'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "tyctx" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"tyctx";
               Elpi.API.PPX.Doc.constructor fmt
                 ~ty:(Elpi.API.ContextualConversion.TyName "prop")
                 ~name:"tentry" ~doc:"TEntry"
                 ~args:[Elpi.API.BuiltInContextualData.nominal.Elpi.API.ContextualConversion.ty;
                       Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.ty;
                       Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_tyctx fmt x);
        embed = elpi_embed_tyctx;
        readback = elpi_readback_tyctx
      }
    let context_made_of_tyctx =
      {
        Elpi.API.ContextualConversion.is_entry_for_nominal = elpi_is_tyctx;
        to_key = elpi_tyctx_to_key;
        push = elpi_push_tyctx;
        pop = elpi_pop_tyctx;
        conv = tyctx;
        init =
          (fun state ->
             Elpi.API.State.set elpi_tyctx_state state
               ((Elpi_tyctx_Map.empty : Elpi.API.RawData.constant
                                          Elpi_tyctx_Map.t),
                 (Elpi.API.RawData.Constants.Map.empty : tyctx
                                                           Elpi.API.ContextualConversion.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get =
          (fun state -> snd @@ (Elpi.API.State.get elpi_tyctx_state state))
      }
    let elpi_tyctx = Elpi.API.BuiltIn.MLDataC tyctx
    class ctx_for_tyctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tyctx.t =
      object (_) inherit  ((Elpi.API.ContextualConversion.ctx) h) end
    let (in_ctx_for_tyctx :
      (Ctx_for_tyctx.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_tyctx) h s), c, (List.concat []))
    let () = declaration := ((!declaration) @ [elpi_tyctx])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let pp_ty _ _ = ()
type ty =
  | TVar of string [@elpi.var tyctx]
  | TApp of string * ty 
  | TAll of bool * string *
  ((ty)[@elpi.binder tyctx (fun b -> fun s -> TEntry (s, b))]) [@@deriving
                                                                 elpi
                                                                   {
                                                                    declaration
                                                                   }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_ty = "ty"
    let elpi_constant_type_tyc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_ty
    let elpi_constant_constructor_ty_TVar = "tvar"
    let elpi_constant_constructor_ty_TVarc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ty_TVar
    let elpi_constant_constructor_ty_TApp = "tapp"
    let elpi_constant_constructor_ty_TAppc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ty_TApp
    let elpi_constant_constructor_ty_TAll = "tall"
    let elpi_constant_constructor_ty_TAllc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ty_TAll
    module Ctx_for_ty =
      struct
        class type t =
          object
            inherit Elpi.API.ContextualConversion.ctx
            inherit Ctx_for_tyctx.t
            method  tyctx : tyctx Elpi.API.ContextualConversion.ctx_field
          end
      end
    let rec elpi_embed_ty :
      'c 'csts .
        (ty, #Ctx_for_ty.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | TVar elpi__29 ->
                  let (elpi__ctx2dbl, _) =
                    Elpi.API.State.get elpi_tyctx_state elpi__state in
                  let elpi__key = (fun x -> x) elpi__29 in
                  (if not (Elpi_tyctx_Map.mem elpi__key elpi__ctx2dbl)
                   then Elpi.API.Utils.error "Unbound variable";
                   (elpi__state,
                     (Elpi.API.RawData.mkBound
                        (Elpi_tyctx_Map.find elpi__key elpi__ctx2dbl)), []))
              | TApp (elpi__32, elpi__33) ->
                  let (elpi__state, elpi__36, elpi__34) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.embed
                                 ~depth h c s t) ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__32 in
                  let (elpi__state, elpi__37, elpi__35) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s -> fun t -> elpi_embed_ty ~depth h c s t)
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__33 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ty_TAppc
                       [elpi__36; elpi__37]),
                    (List.concat [elpi__34; elpi__35]))
              | TAll (elpi__38, elpi__39, elpi__40) ->
                  let (elpi__state, elpi__44, elpi__41) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed
                                 ~depth h c s t) ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__38 in
                  let (elpi__state, elpi__45, elpi__42) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.embed
                                 ~depth h c s t) ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__39 in
                  let elpi__ctx_entry =
                    (fun b -> fun s -> TEntry (s, b)) elpi__38 elpi__39 in
                  let elpi__ctx_key =
                    elpi_tyctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                  let elpi__ctx_entry =
                    {
                      Elpi.API.ContextualConversion.entry = elpi__ctx_entry;
                      depth = elpi__depth
                    } in
                  let elpi__state =
                    elpi_push_tyctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key elpi__ctx_entry in
                  let (elpi__state, elpi__47, elpi__43) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s -> fun t -> elpi_embed_ty ~depth h c s t)
                      ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                      elpi__state elpi__40 in
                  let elpi__46 = Elpi.API.RawData.mkLam elpi__47 in
                  let elpi__state =
                    elpi_pop_tyctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ty_TAllc
                       [elpi__44; elpi__45; elpi__46]),
                    (List.concat [elpi__41; elpi__42; elpi__43]))
    and elpi_readback_ty :
      'c 'csts .
        (ty, #Ctx_for_ty.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.Const elpi__hd when elpi__hd >= 0 ->
                    let (_, elpi__dbl2ctx) =
                      Elpi.API.State.get elpi_tyctx_state elpi__state in
                    (if
                       not
                         (Elpi.API.RawData.Constants.Map.mem elpi__hd
                            elpi__dbl2ctx)
                     then
                       Elpi.API.Utils.error
                         (Format.asprintf "Unbound variable: %s in %a"
                            (Elpi.API.RawData.Constants.show elpi__hd)
                            (Elpi.API.RawData.Constants.Map.pp
                               (Elpi.API.ContextualConversion.pp_ctx_entry
                                  pp_tyctx)) elpi__dbl2ctx);
                     (let {
                            Elpi.API.ContextualConversion.entry = elpi__entry;
                            depth = elpi__depth }
                        =
                        Elpi.API.RawData.Constants.Map.find elpi__hd
                          elpi__dbl2ctx in
                      (elpi__state,
                        (TVar
                           (elpi_tyctx_to_key ~depth:elpi__depth elpi__entry)),
                        [])))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_ty_TAppc ->
                    let (elpi__state, elpi__22, elpi__21) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__19::[] ->
                         let (elpi__state, elpi__19, elpi__20) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t -> elpi_readback_ty ~depth h c s t)
                             ~depth:elpi__depth elpi__hyps elpi__constraints
                             elpi__state elpi__19 in
                         (elpi__state, (TApp (elpi__22, elpi__19)),
                           (List.concat [elpi__21; elpi__20]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_ty_TAppc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_ty_TAllc ->
                    let (elpi__state, elpi__28, elpi__27) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__23::elpi__24::[] ->
                         let (elpi__state, elpi__23, elpi__25) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__23 in
                         let elpi__ctx_entry =
                           (fun b -> fun s -> TEntry (s, b)) elpi__28
                             elpi__23 in
                         let elpi__ctx_key =
                           elpi_tyctx_to_key ~depth:elpi__depth
                             elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi.API.ContextualConversion.entry =
                               elpi__ctx_entry;
                             depth = elpi__depth
                           } in
                         let elpi__state =
                           elpi_push_tyctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key elpi__ctx_entry in
                         let (elpi__state, elpi__24, elpi__26) =
                           match Elpi.API.RawData.look ~depth:elpi__depth
                                   elpi__24
                           with
                           | Elpi.API.RawData.Lam elpi__bo ->
                               ((fun ~depth ->
                                   fun h ->
                                     fun c ->
                                       fun s ->
                                         fun t ->
                                           elpi_readback_ty ~depth h c s t))
                                 ~depth:(elpi__depth + 1) elpi__hyps
                                 elpi__constraints elpi__state elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_tyctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state, (TAll (elpi__28, elpi__23, elpi__24)),
                           (List.concat [elpi__27; elpi__25; elpi__26]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_ty_TAllc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "ty" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and ty :
      'c 'csts .
        (ty, #Ctx_for_ty.t as 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "ty" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"ty";
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tapp"
                 ~doc:"TApp"
                 ~args:[Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyName
                         elpi_constant_type_ty];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tall"
                 ~doc:"TAll"
                 ~args:[Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty;
                       Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("->", (Elpi.API.ContextualConversion.TyName "ty"),
                           [Elpi.API.ContextualConversion.TyName
                              elpi_constant_type_ty])]);
        pp = pp_ty;
        embed = elpi_embed_ty;
        readback = elpi_readback_ty
      }
    let elpi_ty = Elpi.API.BuiltIn.MLDataC ty
    class ctx_for_ty (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_ty.t =
      object (_)
        inherit  ((Elpi.API.ContextualConversion.ctx) h)
        inherit ! ((ctx_for_tyctx) h s)
        method tyctx =
          context_made_of_tyctx.Elpi.API.ContextualConversion.get s
      end
    let (in_ctx_for_ty :
      (Ctx_for_ty.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_tyctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tyctx
                  ctx h c s in
              (s, ((new ctx_for_ty) h s), c, (List.concat [gls0]))
    let () = declaration := ((!declaration) @ [elpi_ty])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let pp_tctx _ _ = ()
type tctx =
  | Entry of ((string)[@elpi.key ]) * ty [@@elpi.index (module String)]
[@@deriving elpi { declaration; context = [tyctx] }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_tctx = "tctx"
    let elpi_constant_type_tctxc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_tctx
    let elpi_constant_constructor_tctx_Entry = "entry"
    let elpi_constant_constructor_tctx_Entryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tctx_Entry
    module Elpi_tctx_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_tctx_state =
      Elpi.API.State.declare ~name:"tctx"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_tctx_Map.empty : Elpi.API.RawData.constant
                                           Elpi_tctx_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : tctx
                                                             Elpi.API.ContextualConversion.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x)
    let elpi_tctx_to_key ~depth:_  =
      function | Entry (elpi__63, _) -> elpi__63
    let elpi_is_tctx { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x } =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_tctx_Entryc)
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
      struct
        class type t =
          object
            inherit Elpi.API.ContextualConversion.ctx
            inherit Ctx_for_tyctx.t
            method  tyctx : tyctx Elpi.API.ContextualConversion.ctx_field
          end
      end
    let rec elpi_embed_tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), #Ctx_for_tctx.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | (elpi__56, Entry (elpi__54, elpi__55)) ->
                  let (elpi__state, elpi__60, elpi__57) =
                    Elpi.API.BuiltInContextualData.nominal.Elpi.API.ContextualConversion.embed
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__56 in
                  let (elpi__state, elpi__61, elpi__58) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.embed
                                 ~depth h c s t) ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__54 in
                  let (elpi__state, elpi__62, elpi__59) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               ty.Elpi.API.ContextualConversion.embed ~depth
                                 h c s t) ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__55 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_tctx_Entryc
                       [elpi__60; elpi__61; elpi__62]),
                    (List.concat [elpi__57; elpi__58; elpi__59]))
    and elpi_readback_tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), #Ctx_for_tctx.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_tctx_Entryc ->
                    let (elpi__state, elpi__53, elpi__52) =
                      Elpi.API.BuiltInContextualData.nominal.Elpi.API.ContextualConversion.readback
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__48::elpi__49::[] ->
                         let (elpi__state, elpi__48, elpi__50) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__48 in
                         let (elpi__state, elpi__49, elpi__51) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      ty.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__49 in
                         (elpi__state,
                           (elpi__53, (Entry (elpi__48, elpi__49))),
                           (List.concat [elpi__52; elpi__50; elpi__51]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_tctx_Entryc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "tctx" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), #Ctx_for_tctx.t as 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "tctx" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"tctx";
               Elpi.API.PPX.Doc.constructor fmt
                 ~ty:(Elpi.API.ContextualConversion.TyName "prop")
                 ~name:"entry" ~doc:"Entry"
                 ~args:[Elpi.API.BuiltInContextualData.nominal.Elpi.API.ContextualConversion.ty;
                       Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.ty;
                       ty.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_tctx fmt x);
        embed = elpi_embed_tctx;
        readback = elpi_readback_tctx
      }
    let context_made_of_tctx =
      {
        Elpi.API.ContextualConversion.is_entry_for_nominal = elpi_is_tctx;
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
                                                           Elpi.API.ContextualConversion.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get =
          (fun state -> snd @@ (Elpi.API.State.get elpi_tctx_state state))
      }
    let elpi_tctx = Elpi.API.BuiltIn.MLDataC tctx
    class ctx_for_tctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tctx.t =
      object (_)
        inherit  ((Elpi.API.ContextualConversion.ctx) h)
        inherit ! ((ctx_for_tyctx) h s)
        method tyctx =
          context_made_of_tyctx.Elpi.API.ContextualConversion.get s
      end
    let (in_ctx_for_tctx :
      (Ctx_for_tctx.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_tyctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tyctx
                  ctx h c s in
              (s, ((new ctx_for_tctx) h s), c, (List.concat [gls0]))
    let () = declaration := ((!declaration) @ [elpi_tctx])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let pp_term _ _ = ()
type term =
  | Var of string [@elpi.var tctx]
  | App of term * term 
  | Lam of ty * string *
  ((term)[@elpi.binder tctx (fun b -> fun s -> Entry (s, b))]) [@@deriving
                                                                 elpi
                                                                   {
                                                                    declaration
                                                                   }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_term = "term"
    let elpi_constant_type_termc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_term
    let elpi_constant_constructor_term_Var = "var"
    let elpi_constant_constructor_term_Varc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Var
    let elpi_constant_constructor_term_App = "app"
    let elpi_constant_constructor_term_Appc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_App
    let elpi_constant_constructor_term_Lam = "lam"
    let elpi_constant_constructor_term_Lamc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Lam
    module Ctx_for_term =
      struct
        class type t =
          object
            inherit Elpi.API.ContextualConversion.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi.API.ContextualConversion.ctx_field
          end
      end
    let rec elpi_embed_term :
      'c 'csts .
        (term, #Ctx_for_term.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | Var elpi__76 ->
                  let (elpi__ctx2dbl, _) =
                    Elpi.API.State.get elpi_tctx_state elpi__state in
                  let elpi__key = (fun x -> x) elpi__76 in
                  (if not (Elpi_tctx_Map.mem elpi__key elpi__ctx2dbl)
                   then Elpi.API.Utils.error "Unbound variable";
                   (elpi__state,
                     (Elpi.API.RawData.mkBound
                        (Elpi_tctx_Map.find elpi__key elpi__ctx2dbl)), []))
              | App (elpi__79, elpi__80) ->
                  let (elpi__state, elpi__83, elpi__81) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s -> fun t -> elpi_embed_term ~depth h c s t)
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__79 in
                  let (elpi__state, elpi__84, elpi__82) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s -> fun t -> elpi_embed_term ~depth h c s t)
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__80 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_term_Appc
                       [elpi__83; elpi__84]),
                    (List.concat [elpi__81; elpi__82]))
              | Lam (elpi__85, elpi__86, elpi__87) ->
                  let (elpi__state, elpi__91, elpi__88) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               ty.Elpi.API.ContextualConversion.embed ~depth
                                 h c s t) ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__85 in
                  let (elpi__state, elpi__92, elpi__89) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.embed
                                 ~depth h c s t) ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__86 in
                  let elpi__ctx_entry =
                    (fun b -> fun s -> Entry (s, b)) elpi__85 elpi__86 in
                  let elpi__ctx_key =
                    elpi_tctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                  let elpi__ctx_entry =
                    {
                      Elpi.API.ContextualConversion.entry = elpi__ctx_entry;
                      depth = elpi__depth
                    } in
                  let elpi__state =
                    elpi_push_tctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key elpi__ctx_entry in
                  let (elpi__state, elpi__94, elpi__90) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s -> fun t -> elpi_embed_term ~depth h c s t)
                      ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                      elpi__state elpi__87 in
                  let elpi__93 = Elpi.API.RawData.mkLam elpi__94 in
                  let elpi__state =
                    elpi_pop_tctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_term_Lamc
                       [elpi__91; elpi__92; elpi__93]),
                    (List.concat [elpi__88; elpi__89; elpi__90]))
    and elpi_readback_term :
      'c 'csts .
        (term, #Ctx_for_term.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
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
                               (Elpi.API.ContextualConversion.pp_ctx_entry
                                  pp_tctx)) elpi__dbl2ctx);
                     (let {
                            Elpi.API.ContextualConversion.entry = elpi__entry;
                            depth = elpi__depth }
                        =
                        Elpi.API.RawData.Constants.Map.find elpi__hd
                          elpi__dbl2ctx in
                      (elpi__state,
                        (Var
                           (elpi_tctx_to_key ~depth:elpi__depth elpi__entry)),
                        [])))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Appc ->
                    let (elpi__state, elpi__69, elpi__68) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t -> elpi_readback_term ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__66::[] ->
                         let (elpi__state, elpi__66, elpi__67) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      elpi_readback_term ~depth h c s t)
                             ~depth:elpi__depth elpi__hyps elpi__constraints
                             elpi__state elpi__66 in
                         (elpi__state, (App (elpi__69, elpi__66)),
                           (List.concat [elpi__68; elpi__67]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Appc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Lamc ->
                    let (elpi__state, elpi__75, elpi__74) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 ty.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__70::elpi__71::[] ->
                         let (elpi__state, elpi__70, elpi__72) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__70 in
                         let elpi__ctx_entry =
                           (fun b -> fun s -> Entry (s, b)) elpi__75 elpi__70 in
                         let elpi__ctx_key =
                           elpi_tctx_to_key ~depth:elpi__depth
                             elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi.API.ContextualConversion.entry =
                               elpi__ctx_entry;
                             depth = elpi__depth
                           } in
                         let elpi__state =
                           elpi_push_tctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key elpi__ctx_entry in
                         let (elpi__state, elpi__71, elpi__73) =
                           match Elpi.API.RawData.look ~depth:elpi__depth
                                   elpi__71
                           with
                           | Elpi.API.RawData.Lam elpi__bo ->
                               ((fun ~depth ->
                                   fun h ->
                                     fun c ->
                                       fun s ->
                                         fun t ->
                                           elpi_readback_term ~depth h c s t))
                                 ~depth:(elpi__depth + 1) elpi__hyps
                                 elpi__constraints elpi__state elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_tctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state, (Lam (elpi__75, elpi__70, elpi__71)),
                           (List.concat [elpi__74; elpi__72; elpi__73]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Lamc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "term" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and term :
      'c 'csts .
        (term, #Ctx_for_term.t as 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "term" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"term";
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"app"
                 ~doc:"App"
                 ~args:[Elpi.API.ContextualConversion.TyName
                          elpi_constant_type_term;
                       Elpi.API.ContextualConversion.TyName
                         elpi_constant_type_term];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"lam"
                 ~doc:"Lam"
                 ~args:[ty.Elpi.API.ContextualConversion.ty;
                       Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("->",
                           (Elpi.API.ContextualConversion.TyName "term"),
                           [Elpi.API.ContextualConversion.TyName
                              elpi_constant_type_term])]);
        pp = pp_term;
        embed = elpi_embed_term;
        readback = elpi_readback_term
      }
    let elpi_term = Elpi.API.BuiltIn.MLDataC term
    class ctx_for_term (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_term.t =
      object (_)
        inherit  ((Elpi.API.ContextualConversion.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx =
          context_made_of_tctx.Elpi.API.ContextualConversion.get s
      end
    let (in_ctx_for_term :
      (Ctx_for_term.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_tctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tctx ctx
                  h c s in
              (s, ((new ctx_for_term) h s), c, (List.concat [gls0]))
    let () = declaration := ((!declaration) @ [elpi_term])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let _ = fun (f : #ctx_for_tctx -> unit) -> fun (x : ctx_for_term) -> f x
open Elpi.API
open BuiltInPredicate
open Notation
let term_to_string =
  CPred
    ("term->string", in_ctx_for_term,
      (CIn
         (term, "T",
           (COut (BuiltInContextualData.string, "S", (CRead "what else"))))),
      (fun (t : term) ->
         fun (_ety : string oarg) ->
           fun ~depth:_ ->
             fun c ->
               fun (_cst : Data.constraints) ->
                 fun (_state : State.t) ->
                   !:
                     (Format.asprintf "@[<hov>%a@ ; %a@ |-@ %a@]@\n%!"
                        (RawData.Constants.Map.pp
                           (ContextualConversion.pp_ctx_entry pp_tctx))
                        c#tyctx
                        (RawData.Constants.Map.pp
                           (ContextualConversion.pp_ctx_entry pp_tctx))
                        c#tctx term.pp t)))
let builtin1 =
  let open BuiltIn in
    declare ~file_name:"test_ppx.elpi"
      ((!declaration) @
         ([MLCode (term_to_string, DocAbove);
          LPDoc "----------------- elpi ----------------"] @
            (let open Elpi.Builtin in core_builtins @ elpi_builtins)))
let builtin2 =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!declaration)
let main () =
  let _elpi = Setup.init ~builtins:[builtin1; builtin2] () in
  BuiltIn.document_file builtin2; exit 0
;;main ()
