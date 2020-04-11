let elpi_stuff = ref []
module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show = Format.asprintf "%a" pp
  end
let pp_tctx _ _ = ()
type tctx =
  | TEntry of ((string)[@elpi.key ]) * bool [@@deriving
                                              elpi
                                                {
                                                  declaration = elpi_stuff;
                                                  index = (module String)
                                                }]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_tctx = "tctx"
    let elpi_constant_type_tctxc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_tctx
    let elpi_constant_constructor_tctx_TEntry = "tentry"
    let elpi_constant_constructor_tctx_TEntryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tctx_TEntry
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
    let elpi_tctx_to_key ~depth:_  =
      function | TEntry (elpi__1, _) -> elpi__1
    let elpi_is_tctx ~depth:elpi__depth  elpi__x =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_tctx_TEntryc)
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
    let rec elpi_embed_tctx :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        ((Elpi.API.RawData.constant * tctx), 'elpi__param__poly_hyps,
          'elpi__param__poly_csts) Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | (elpi__10, TEntry (elpi__8, elpi__9)) ->
                  let (elpi__state, elpi__14, elpi__11) =
                    Elpi.API.PPX.embed_nominal ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__10 in
                  let (elpi__state, elpi__15, elpi__12) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__8 in
                  let (elpi__state, elpi__16, elpi__13) =
                    Elpi.Builtin.PPX.embed_bool ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__9 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_tctx_TEntryc
                       [elpi__14; elpi__15; elpi__16]),
                    (List.concat [elpi__11; elpi__12; elpi__13]))
    let rec elpi_readback_tctx :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        ((Elpi.API.RawData.constant * tctx), 'elpi__param__poly_hyps,
          'elpi__param__poly_csts) Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_tctx_TEntryc ->
                    let (elpi__state, elpi__7, elpi__6) =
                      Elpi.API.PPX.readback_nominal ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__2::elpi__3::[] ->
                         let (elpi__state, elpi__2, elpi__4) =
                           Elpi.API.PPX.readback_string ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__2 in
                         let (elpi__state, elpi__3, elpi__5) =
                           Elpi.Builtin.PPX.readback_bool ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__3 in
                         (elpi__state,
                           (elpi__7, (TEntry (elpi__2, elpi__3))),
                           (List.concat [elpi__6; elpi__4; elpi__5]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_tctx_TEntryc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "tctx" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    let tctx :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        ((Elpi.API.RawData.constant * tctx), 'elpi__param__poly_hyps,
          'elpi__param__poly_csts) Elpi.API.ContextualConversion.t
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
                 ~name:"tentry" ~doc:"TEntry"
                 ~args:[Elpi.API.PPX.nominal.Elpi.API.ContextualConversion.ty;
                       (Elpi.API.ContextualConversion.(!>)
                          Elpi.API.BuiltInData.string).Elpi.API.ContextualConversion.ty;
                       (Elpi.API.ContextualConversion.(!>) Elpi.Builtin.bool).Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_tctx fmt x);
        embed = elpi_embed_tctx;
        readback = elpi_readback_tctx
      }
    let in_tctx_alone ~depth:elpi__depth  elpi__hyps elpi__constraints
      elpi__state =
      let module CMap = Elpi.API.RawData.Constants.Map in
        let elpi__filtered_hyps =
          List.fold_left
            (fun elpi__m ->
               fun
                 ({ Elpi.API.RawData.hdepth = elpi__i; hsrc = elpi__hsrc } as
                    elpi__hyp)
                 ->
                 match elpi_is_tctx ~depth:elpi__i elpi__hsrc with
                 | None -> elpi__m
                 | Some elpi__idx ->
                     (if CMap.mem elpi__idx elpi__m
                      then
                        Elpi.API.Utils.type_error
                          "more than one context entry for the same nominal";
                      CMap.add elpi__idx elpi__hyp elpi__m)) CMap.empty
            (Elpi.API.RawData.of_hyps elpi__hyps) in
        let rec elpi__aux elpi__state elpi__gls elpi__i =
          if elpi__i = elpi__depth
          then (elpi__state, (List.concat (List.rev elpi__gls)))
          else
            if not (CMap.mem elpi__i elpi__filtered_hyps)
            then elpi__aux elpi__state elpi__gls (elpi__i + 1)
            else
              (let elpi__hyp = CMap.find elpi__i elpi__filtered_hyps in
               let elpi__hyp_depth = elpi__hyp.Elpi.API.RawData.hdepth in
               let (elpi__state, (elpi__nominal, elpi__t), elpi__gls_t) =
                 tctx.Elpi.API.ContextualConversion.readback
                   ~depth:elpi__hyp_depth elpi__hyps elpi__constraints
                   elpi__state elpi__hyp.Elpi.API.RawData.hsrc in
               assert (elpi__nominal = elpi__i);
               (let elpi__s = elpi_tctx_to_key ~depth:elpi__hyp_depth elpi__t in
                let elpi__state =
                  elpi_push_tctx ~depth:elpi__i elpi__state elpi__s
                    {
                      Elpi.API.ContextualConversion.entry = elpi__t;
                      depth = elpi__hyp_depth
                    } in
                elpi__aux elpi__state (elpi__gls_t :: elpi__gls)
                  (elpi__i + 1))) in
        let elpi__state =
          Elpi.API.State.set elpi_tctx_state elpi__state
            (Elpi_tctx_Map.empty, CMap.empty) in
        let (elpi__state, elpi__gls) = elpi__aux elpi__state [] 0 in
        let (_, elpi__dbl2ctx) =
          Elpi.API.State.get elpi_tctx_state elpi__state in
        (elpi__state, elpi__dbl2ctx, elpi__constraints, elpi__gls)
    let in_tctx = in_tctx_alone
    let elpi_tctx = Elpi.API.BuiltIn.MLDataC tctx
    let () = elpi_stuff := ((!elpi_stuff) @ [elpi_tctx])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let pp_ty _ _ = ()
type ty =
  | TVar of string [@elpi.var ]
  | TApp of string * ty 
  | TAll of bool * string *
  ((ty)[@elpi.binder fun b -> fun s -> TEntry (s, b)]) [@@deriving
                                                         elpi
                                                           {
                                                             declaration =
                                                               elpi_stuff;
                                                             context =
                                                               (() : 
                                                               ty -> 
                                                                 tctx)
                                                           }]
include
  struct
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
    let rec elpi_embed_ty :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (ty, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | TVar elpi__29 ->
                  let (elpi__ctx2dbl, _) =
                    Elpi.API.State.get elpi_tctx_state elpi__state in
                  let elpi__key = (fun x -> x) elpi__29 in
                  (if not (Elpi_tctx_Map.mem elpi__key elpi__ctx2dbl)
                   then Elpi.API.Utils.error "Unbound variable";
                   (elpi__state,
                     (Elpi.API.RawData.mkBound
                        (Elpi_tctx_Map.find elpi__key elpi__ctx2dbl)), []))
              | TApp (elpi__32, elpi__33) ->
                  let (elpi__state, elpi__36, elpi__34) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__32 in
                  let (elpi__state, elpi__37, elpi__35) =
                    elpi_embed_ty ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__33 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ty_TAppc
                       [elpi__36; elpi__37]),
                    (List.concat [elpi__34; elpi__35]))
              | TAll (elpi__38, elpi__39, elpi__40) ->
                  let (elpi__state, elpi__44, elpi__41) =
                    Elpi.Builtin.PPX.embed_bool ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__38 in
                  let (elpi__state, elpi__45, elpi__42) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__39 in
                  let elpi__ctx_entry =
                    (fun b -> fun s -> TEntry (s, b)) elpi__38 elpi__39 in
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
                  let (elpi__state, elpi__47, elpi__43) =
                    elpi_embed_ty ~depth:(elpi__depth + 1) elpi__hyps
                      elpi__constraints elpi__state elpi__40 in
                  let elpi__46 = Elpi.API.RawData.mkLam elpi__47 in
                  let elpi__state =
                    elpi_pop_tctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ty_TAllc
                       [elpi__44; elpi__45; elpi__46]),
                    (List.concat [elpi__41; elpi__42; elpi__43]))
    let rec elpi_readback_ty :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (ty, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
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
                        (TVar
                           (elpi_tctx_to_key ~depth:elpi__depth elpi__entry)),
                        [])))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_ty_TAppc ->
                    let (elpi__state, elpi__22, elpi__21) =
                      Elpi.API.PPX.readback_string ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__19::[] ->
                         let (elpi__state, elpi__19, elpi__20) =
                           elpi_readback_ty ~depth:elpi__depth elpi__hyps
                             elpi__constraints elpi__state elpi__19 in
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
                      Elpi.Builtin.PPX.readback_bool ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__23::elpi__24::[] ->
                         let (elpi__state, elpi__23, elpi__25) =
                           Elpi.API.PPX.readback_string ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__23 in
                         let elpi__ctx_entry =
                           (fun b -> fun s -> TEntry (s, b)) elpi__28
                             elpi__23 in
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
                         let (elpi__state, elpi__24, elpi__26) =
                           match Elpi.API.RawData.look ~depth:elpi__depth
                                   elpi__24
                           with
                           | Elpi.API.RawData.Lam elpi__bo ->
                               elpi_readback_ty ~depth:(elpi__depth + 1)
                                 elpi__hyps elpi__constraints elpi__state
                                 elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_tctx ~depth:elpi__depth elpi__state
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
    let ty :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (ty, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.t
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
                 ~args:[(Elpi.API.ContextualConversion.(!>)
                           Elpi.API.BuiltInData.string).Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyName
                         elpi_constant_type_ty];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tall"
                 ~doc:"TAll"
                 ~args:[(Elpi.API.ContextualConversion.(!>) Elpi.Builtin.bool).Elpi.API.ContextualConversion.ty;
                       (Elpi.API.ContextualConversion.(!>)
                          Elpi.API.BuiltInData.string).Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("->", (Elpi.API.ContextualConversion.TyName "ty"),
                           [Elpi.API.ContextualConversion.TyName
                              elpi_constant_type_ty])]);
        pp = pp_ty;
        embed = elpi_embed_ty;
        readback = elpi_readback_ty
      }
    let elpi_ty = Elpi.API.BuiltIn.MLDataC ty
    let () = elpi_stuff := ((!elpi_stuff) @ [elpi_ty])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let pp_ctx _ _ = ()
type ctx =
  | Entry of ((string)[@elpi.key ]) * ty [@@deriving
                                           elpi
                                             {
                                               declaration = elpi_stuff;
                                               index = (module String);
                                               context = (() : tctx)
                                             }]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_ctx = "ctx"
    let elpi_constant_type_ctxc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_ctx
    let elpi_constant_constructor_ctx_Entry = "entry"
    let elpi_constant_constructor_ctx_Entryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ctx_Entry
    module Elpi_ctx_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_ctx_state =
      Elpi.API.State.declare ~name:"ctx"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_ctx_Map.empty : Elpi.API.RawData.constant
                                          Elpi_ctx_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : ctx
                                                             Elpi.API.ContextualConversion.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
    let elpi_ctx_to_key ~depth:_  =
      function | Entry (elpi__48, _) -> elpi__48
    let elpi_is_ctx ~depth:elpi__depth  elpi__x =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_ctx_Entryc)
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
    let rec elpi_embed_ctx :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        ((Elpi.API.RawData.constant * ctx), 'elpi__param__poly_hyps,
          'elpi__param__poly_csts) Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | (elpi__57, Entry (elpi__55, elpi__56)) ->
                  let (elpi__state, elpi__61, elpi__58) =
                    Elpi.API.PPX.embed_nominal ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__57 in
                  let (elpi__state, elpi__62, elpi__59) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__55 in
                  let (elpi__state, elpi__63, elpi__60) =
                    ty.Elpi.API.ContextualConversion.embed ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__56 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ctx_Entryc
                       [elpi__61; elpi__62; elpi__63]),
                    (List.concat [elpi__58; elpi__59; elpi__60]))
    let rec elpi_readback_ctx :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        ((Elpi.API.RawData.constant * ctx), 'elpi__param__poly_hyps,
          'elpi__param__poly_csts) Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_ctx_Entryc ->
                    let (elpi__state, elpi__54, elpi__53) =
                      Elpi.API.PPX.readback_nominal ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__49::elpi__50::[] ->
                         let (elpi__state, elpi__49, elpi__51) =
                           Elpi.API.PPX.readback_string ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__49 in
                         let (elpi__state, elpi__50, elpi__52) =
                           ty.Elpi.API.ContextualConversion.readback
                             ~depth:elpi__depth elpi__hyps elpi__constraints
                             elpi__state elpi__50 in
                         (elpi__state,
                           (elpi__54, (Entry (elpi__49, elpi__50))),
                           (List.concat [elpi__53; elpi__51; elpi__52]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_ctx_Entryc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "ctx" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    let ctx :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        ((Elpi.API.RawData.constant * ctx), 'elpi__param__poly_hyps,
          'elpi__param__poly_csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "ctx" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"ctx";
               Elpi.API.PPX.Doc.constructor fmt
                 ~ty:(Elpi.API.ContextualConversion.TyName "prop")
                 ~name:"entry" ~doc:"Entry"
                 ~args:[Elpi.API.PPX.nominal.Elpi.API.ContextualConversion.ty;
                       (Elpi.API.ContextualConversion.(!>)
                          Elpi.API.BuiltInData.string).Elpi.API.ContextualConversion.ty;
                       ty.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_ctx fmt x);
        embed = elpi_embed_ctx;
        readback = elpi_readback_ctx
      }
    let in_ctx_alone ~depth:elpi__depth  elpi__hyps elpi__constraints
      elpi__state =
      let module CMap = Elpi.API.RawData.Constants.Map in
        let elpi__filtered_hyps =
          List.fold_left
            (fun elpi__m ->
               fun
                 ({ Elpi.API.RawData.hdepth = elpi__i; hsrc = elpi__hsrc } as
                    elpi__hyp)
                 ->
                 match elpi_is_ctx ~depth:elpi__i elpi__hsrc with
                 | None -> elpi__m
                 | Some elpi__idx ->
                     (if CMap.mem elpi__idx elpi__m
                      then
                        Elpi.API.Utils.type_error
                          "more than one context entry for the same nominal";
                      CMap.add elpi__idx elpi__hyp elpi__m)) CMap.empty
            (Elpi.API.RawData.of_hyps elpi__hyps) in
        let rec elpi__aux elpi__state elpi__gls elpi__i =
          if elpi__i = elpi__depth
          then (elpi__state, (List.concat (List.rev elpi__gls)))
          else
            if not (CMap.mem elpi__i elpi__filtered_hyps)
            then elpi__aux elpi__state elpi__gls (elpi__i + 1)
            else
              (let elpi__hyp = CMap.find elpi__i elpi__filtered_hyps in
               let elpi__hyp_depth = elpi__hyp.Elpi.API.RawData.hdepth in
               let (elpi__state, (elpi__nominal, elpi__t), elpi__gls_t) =
                 ctx.Elpi.API.ContextualConversion.readback
                   ~depth:elpi__hyp_depth elpi__hyps elpi__constraints
                   elpi__state elpi__hyp.Elpi.API.RawData.hsrc in
               assert (elpi__nominal = elpi__i);
               (let elpi__s = elpi_ctx_to_key ~depth:elpi__hyp_depth elpi__t in
                let elpi__state =
                  elpi_push_ctx ~depth:elpi__i elpi__state elpi__s
                    {
                      Elpi.API.ContextualConversion.entry = elpi__t;
                      depth = elpi__hyp_depth
                    } in
                elpi__aux elpi__state (elpi__gls_t :: elpi__gls)
                  (elpi__i + 1))) in
        let elpi__state =
          Elpi.API.State.set elpi_ctx_state elpi__state
            (Elpi_ctx_Map.empty, CMap.empty) in
        let (elpi__state, elpi__gls) = elpi__aux elpi__state [] 0 in
        let (_, elpi__dbl2ctx) =
          Elpi.API.State.get elpi_ctx_state elpi__state in
        (elpi__state, elpi__dbl2ctx, elpi__constraints, elpi__gls)
    let in_ctx =
      Elpi.API.ContextualConversion.(|+|) in_tctx_alone in_ctx_alone
    let elpi_ctx = Elpi.API.BuiltIn.MLDataC ctx
    let () = elpi_stuff := ((!elpi_stuff) @ [elpi_ctx])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let pp_term _ _ = ()
type term =
  | Var of string [@elpi.var ]
  | App of term * term 
  | Lam of ty * string *
  ((term)[@elpi.binder fun b -> fun s -> Entry (s, b)]) [@@deriving
                                                          elpi
                                                            {
                                                              declaration =
                                                                elpi_stuff;
                                                              context =
                                                                (() : 
                                                                ((ty -> tctx)
                                                                  *
                                                                  (term ->
                                                                    ctx)))
                                                            }]
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
    let elpi_constant_constructor_term_App = "app"
    let elpi_constant_constructor_term_Appc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_App
    let elpi_constant_constructor_term_Lam = "lam"
    let elpi_constant_constructor_term_Lamc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Lam
    let rec elpi_embed_term :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (term, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | Var elpi__76 ->
                  let (elpi__ctx2dbl, _) =
                    Elpi.API.State.get elpi_ctx_state elpi__state in
                  let elpi__key = (fun x -> x) elpi__76 in
                  (if not (Elpi_ctx_Map.mem elpi__key elpi__ctx2dbl)
                   then Elpi.API.Utils.error "Unbound variable";
                   (elpi__state,
                     (Elpi.API.RawData.mkBound
                        (Elpi_ctx_Map.find elpi__key elpi__ctx2dbl)), []))
              | App (elpi__79, elpi__80) ->
                  let (elpi__state, elpi__83, elpi__81) =
                    elpi_embed_term ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__79 in
                  let (elpi__state, elpi__84, elpi__82) =
                    elpi_embed_term ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__80 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_term_Appc
                       [elpi__83; elpi__84]),
                    (List.concat [elpi__81; elpi__82]))
              | Lam (elpi__85, elpi__86, elpi__87) ->
                  let (elpi__state, elpi__91, elpi__88) =
                    ty.Elpi.API.ContextualConversion.embed ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__85 in
                  let (elpi__state, elpi__92, elpi__89) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__86 in
                  let elpi__ctx_entry =
                    (fun b -> fun s -> Entry (s, b)) elpi__85 elpi__86 in
                  let elpi__ctx_key =
                    elpi_ctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                  let elpi__ctx_entry =
                    {
                      Elpi.API.ContextualConversion.entry = elpi__ctx_entry;
                      depth = elpi__depth
                    } in
                  let elpi__state =
                    elpi_push_ctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key elpi__ctx_entry in
                  let (elpi__state, elpi__94, elpi__90) =
                    elpi_embed_term ~depth:(elpi__depth + 1) elpi__hyps
                      elpi__constraints elpi__state elpi__87 in
                  let elpi__93 = Elpi.API.RawData.mkLam elpi__94 in
                  let elpi__state =
                    elpi_pop_ctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_term_Lamc
                       [elpi__91; elpi__92; elpi__93]),
                    (List.concat [elpi__88; elpi__89; elpi__90]))
    let rec elpi_readback_term :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (term, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
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
                               (Elpi.API.ContextualConversion.pp_ctx_entry
                                  pp_ctx)) elpi__dbl2ctx);
                     (let {
                            Elpi.API.ContextualConversion.entry = elpi__entry;
                            depth = elpi__depth }
                        =
                        Elpi.API.RawData.Constants.Map.find elpi__hd
                          elpi__dbl2ctx in
                      (elpi__state,
                        (Var (elpi_ctx_to_key ~depth:elpi__depth elpi__entry)),
                        [])))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Appc ->
                    let (elpi__state, elpi__69, elpi__68) =
                      elpi_readback_term ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__66::[] ->
                         let (elpi__state, elpi__66, elpi__67) =
                           elpi_readback_term ~depth:elpi__depth elpi__hyps
                             elpi__constraints elpi__state elpi__66 in
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
                      ty.Elpi.API.ContextualConversion.readback
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__70::elpi__71::[] ->
                         let (elpi__state, elpi__70, elpi__72) =
                           Elpi.API.PPX.readback_string ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__70 in
                         let elpi__ctx_entry =
                           (fun b -> fun s -> Entry (s, b)) elpi__75 elpi__70 in
                         let elpi__ctx_key =
                           elpi_ctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi.API.ContextualConversion.entry =
                               elpi__ctx_entry;
                             depth = elpi__depth
                           } in
                         let elpi__state =
                           elpi_push_ctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key elpi__ctx_entry in
                         let (elpi__state, elpi__71, elpi__73) =
                           match Elpi.API.RawData.look ~depth:elpi__depth
                                   elpi__71
                           with
                           | Elpi.API.RawData.Lam elpi__bo ->
                               elpi_readback_term ~depth:(elpi__depth + 1)
                                 elpi__hyps elpi__constraints elpi__state
                                 elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_ctx ~depth:elpi__depth elpi__state
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
    let term :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (term, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.t
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
                       (Elpi.API.ContextualConversion.(!>)
                          Elpi.API.BuiltInData.string).Elpi.API.ContextualConversion.ty;
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
    let () = elpi_stuff := ((!elpi_stuff) @ [elpi_term])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
open Elpi.API
let in_ctx
  : ((tctx ContextualConversion.ctx_entry RawData.Constants.Map.t * ctx
       ContextualConversion.ctx_entry RawData.Constants.Map.t),
      Data.constraints) ContextualConversion.ctx_readback
  = in_ctx
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
