let declaration = ref []
module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show = Format.asprintf "%a" pp
  end
type term =
  | Var of string [@elpi.var ctx]
  | App of term * term 
  | Tapp of term * ty 
  | Lam of ty * string *
  ((term)[@elpi.binder ctx (fun b -> fun s -> Entry (s, b))]) 
and ty =
  | TVar of string [@elpi.var ctx]
  | TIdx of ty * term 
  | TAbs of string * bool *
  ((ty)[@elpi.binder ctx (fun s -> fun b -> TEntry (s, b))]) 
and ctx =
  | Entry of ((string)[@elpi.index ]) * ty 
  | TEentry of ((string)[@elpi.index ]) * bool [@@elpi.index (module String)]
[@@deriving elpi { declaration }]
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
    let elpi_constant_constructor_term_Tapp = "tapp"
    let elpi_constant_constructor_term_Tappc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Tapp
    let elpi_constant_constructor_term_Lam = "lam"
    let elpi_constant_constructor_term_Lamc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Lam
    let elpi_constant_type_ty = "ty"
    let elpi_constant_type_tyc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_ty
    let elpi_constant_constructor_ty_TVar = "tvar"
    let elpi_constant_constructor_ty_TVarc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ty_TVar
    let elpi_constant_constructor_ty_TIdx = "tidx"
    let elpi_constant_constructor_ty_TIdxc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ty_TIdx
    let elpi_constant_constructor_ty_TAbs = "tabs"
    let elpi_constant_constructor_ty_TAbsc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ty_TAbs
    let elpi_constant_type_ctx = "ctx"
    let elpi_constant_type_ctxc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_ctx
    let elpi_constant_constructor_ctx_Entry = "entry"
    let elpi_constant_constructor_ctx_Entryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ctx_Entry
    let elpi_constant_constructor_ctx_TEentry = "teentry"
    let elpi_constant_constructor_ctx_TEentryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_ctx_TEentry
    module Ctx_for_term =
      struct
        class type t =
          object
            inherit Elpi.API.Conversion.ctx
            inherit Ctx_for_ctx.t
            method  ctx : ctx Elpi.API.Conversion.ctx_field
          end
      end
    module Ctx_for_ty =
      struct
        class type t =
          object
            inherit Elpi.API.Conversion.ctx
            inherit Ctx_for_ctx.t
            method  ctx : ctx Elpi.API.Conversion.ctx_field
          end
      end
    module Ctx_for_ctx =
      struct
        class type t =
          object
            inherit Elpi.API.Conversion.ctx
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
              | Var elpi__17 ->
                  let (elpi__ctx2dbl, _) =
                    Elpi.API.State.get elpi_ctx_state elpi__state in
                  let elpi__key = (fun x -> x) elpi__17 in
                  (if not (Elpi_ctx_Map.mem elpi__key elpi__ctx2dbl)
                   then Elpi.API.Utils.error "Unbound variable";
                   (elpi__state,
                     (Elpi.API.RawData.mkBound
                        (Elpi_ctx_Map.find elpi__key elpi__ctx2dbl)), []))
              | App (elpi__20, elpi__21) ->
                  let (elpi__state, elpi__24, elpi__22) =
                    elpi_embed_term ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__20 in
                  let (elpi__state, elpi__25, elpi__23) =
                    elpi_embed_term ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__21 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_term_Appc
                       [elpi__24; elpi__25]),
                    (List.concat [elpi__22; elpi__23]))
              | Tapp (elpi__26, elpi__27) ->
                  let (elpi__state, elpi__30, elpi__28) =
                    elpi_embed_term ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__26 in
                  let (elpi__state, elpi__31, elpi__29) =
                    elpi_embed_ty ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__27 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_term_Tappc
                       [elpi__30; elpi__31]),
                    (List.concat [elpi__28; elpi__29]))
              | Lam (elpi__32, elpi__33, elpi__34) ->
                  let (elpi__state, elpi__38, elpi__35) =
                    elpi_embed_ty ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__32 in
                  let (elpi__state, elpi__39, elpi__36) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__33 in
                  let elpi__ctx_entry =
                    (fun b -> fun s -> Entry (s, b)) elpi__32 elpi__33 in
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
                  let (elpi__state, elpi__41, elpi__37) =
                    elpi_embed_term ~depth:(elpi__depth + 1) elpi__hyps
                      elpi__constraints elpi__state elpi__34 in
                  let elpi__40 = Elpi.API.RawData.mkLam elpi__41 in
                  let elpi__state =
                    elpi_pop_ctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_term_Lamc
                       [elpi__38; elpi__39; elpi__40]),
                    (List.concat [elpi__35; elpi__36; elpi__37]))
    and elpi_embed_ty :
      'c . (ty, #Ctx_for_ty.t as 'c) Elpi.API.Conversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | TVar elpi__54 ->
                  let (elpi__ctx2dbl, _) =
                    Elpi.API.State.get elpi_ctx_state elpi__state in
                  let elpi__key = (fun x -> x) elpi__54 in
                  (if not (Elpi_ctx_Map.mem elpi__key elpi__ctx2dbl)
                   then Elpi.API.Utils.error "Unbound variable";
                   (elpi__state,
                     (Elpi.API.RawData.mkBound
                        (Elpi_ctx_Map.find elpi__key elpi__ctx2dbl)), []))
              | TIdx (elpi__57, elpi__58) ->
                  let (elpi__state, elpi__61, elpi__59) =
                    elpi_embed_ty ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__57 in
                  let (elpi__state, elpi__62, elpi__60) =
                    elpi_embed_term ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__58 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ty_TIdxc
                       [elpi__61; elpi__62]),
                    (List.concat [elpi__59; elpi__60]))
              | TAbs (elpi__63, elpi__64, elpi__65) ->
                  let (elpi__state, elpi__69, elpi__66) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__63 in
                  let (elpi__state, elpi__70, elpi__67) =
                    Elpi.Builtin.PPX.embed_bool ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__64 in
                  let elpi__ctx_entry =
                    (fun s -> fun b -> TEntry (s, b)) elpi__63 elpi__64 in
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
                  let (elpi__state, elpi__72, elpi__68) =
                    elpi_embed_ty ~depth:(elpi__depth + 1) elpi__hyps
                      elpi__constraints elpi__state elpi__65 in
                  let elpi__71 = Elpi.API.RawData.mkLam elpi__72 in
                  let elpi__state =
                    elpi_pop_ctx ~depth:(elpi__depth + 1) elpi__state
                      elpi__ctx_key in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ty_TAbsc
                       [elpi__69; elpi__70; elpi__71]),
                    (List.concat [elpi__66; elpi__67; elpi__68]))
    and elpi_embed_ctx :
      'c .
        ((Elpi.API.RawData.constant * ctx), #Ctx_for_ctx.t as 'c)
          Elpi.API.Conversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | (elpi__87, Entry (elpi__85, elpi__86)) ->
                  let (elpi__state, elpi__91, elpi__88) =
                    Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.embed
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__87 in
                  let (elpi__state, elpi__92, elpi__89) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__85 in
                  let (elpi__state, elpi__93, elpi__90) =
                    elpi_embed_ty ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__86 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ctx_Entryc
                       [elpi__91; elpi__92; elpi__93]),
                    (List.concat [elpi__88; elpi__89; elpi__90]))
              | (elpi__96, TEentry (elpi__94, elpi__95)) ->
                  let (elpi__state, elpi__100, elpi__97) =
                    Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.embed
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__96 in
                  let (elpi__state, elpi__101, elpi__98) =
                    Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__94 in
                  let (elpi__state, elpi__102, elpi__99) =
                    Elpi.Builtin.PPX.embed_bool ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__95 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_ctx_TEentryc
                       [elpi__100; elpi__101; elpi__102]),
                    (List.concat [elpi__97; elpi__98; elpi__99]))
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
                    let (elpi__state, elpi__6, elpi__5) =
                      elpi_readback_term ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__3::[] ->
                         let (elpi__state, elpi__3, elpi__4) =
                           elpi_readback_term ~depth:elpi__depth elpi__hyps
                             elpi__constraints elpi__state elpi__3 in
                         (elpi__state, (App (elpi__6, elpi__3)),
                           (List.concat [elpi__5; elpi__4]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Appc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Tappc ->
                    let (elpi__state, elpi__10, elpi__9) =
                      elpi_readback_term ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__7::[] ->
                         let (elpi__state, elpi__7, elpi__8) =
                           elpi_readback_ty ~depth:elpi__depth elpi__hyps
                             elpi__constraints elpi__state elpi__7 in
                         (elpi__state, (Tapp (elpi__10, elpi__7)),
                           (List.concat [elpi__9; elpi__8]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Tappc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Lamc ->
                    let (elpi__state, elpi__16, elpi__15) =
                      elpi_readback_ty ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__11::elpi__12::[] ->
                         let (elpi__state, elpi__11, elpi__13) =
                           Elpi.API.PPX.readback_string ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__11 in
                         let elpi__ctx_entry =
                           (fun b -> fun s -> Entry (s, b)) elpi__16 elpi__11 in
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
                         let (elpi__state, elpi__12, elpi__14) =
                           match Elpi.API.RawData.look ~depth:elpi__depth
                                   elpi__12
                           with
                           | Elpi.API.RawData.Lam elpi__bo ->
                               elpi_readback_term ~depth:(elpi__depth + 1)
                                 elpi__hyps elpi__constraints elpi__state
                                 elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_ctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state, (Lam (elpi__16, elpi__11, elpi__12)),
                           (List.concat [elpi__15; elpi__13; elpi__14]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Lamc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "term" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and elpi_readback_ty :
      'c . (ty, #Ctx_for_ty.t as 'c) Elpi.API.Conversion.readback =
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
                        (TVar
                           (elpi_ctx_to_key ~depth:elpi__depth elpi__entry)),
                        [])))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_ty_TIdxc ->
                    let (elpi__state, elpi__47, elpi__46) =
                      elpi_readback_ty ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__44::[] ->
                         let (elpi__state, elpi__44, elpi__45) =
                           elpi_readback_term ~depth:elpi__depth elpi__hyps
                             elpi__constraints elpi__state elpi__44 in
                         (elpi__state, (TIdx (elpi__47, elpi__44)),
                           (List.concat [elpi__46; elpi__45]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_ty_TIdxc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_ty_TAbsc ->
                    let (elpi__state, elpi__53, elpi__52) =
                      Elpi.API.PPX.readback_string ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__48::elpi__49::[] ->
                         let (elpi__state, elpi__48, elpi__50) =
                           Elpi.Builtin.PPX.readback_bool ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__48 in
                         let elpi__ctx_entry =
                           (fun s -> fun b -> TEntry (s, b)) elpi__53
                             elpi__48 in
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
                         let (elpi__state, elpi__49, elpi__51) =
                           match Elpi.API.RawData.look ~depth:elpi__depth
                                   elpi__49
                           with
                           | Elpi.API.RawData.Lam elpi__bo ->
                               elpi_readback_ty ~depth:(elpi__depth + 1)
                                 elpi__hyps elpi__constraints elpi__state
                                 elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_ctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state, (TAbs (elpi__53, elpi__48, elpi__49)),
                           (List.concat [elpi__52; elpi__50; elpi__51]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_ty_TAbsc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "ty" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and elpi_readback_ctx :
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
                    elpi__hd == elpi_constant_constructor_ctx_Entryc ->
                    let (elpi__state, elpi__78, elpi__77) =
                      Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.readback
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__73::elpi__74::[] ->
                         let (elpi__state, elpi__73, elpi__75) =
                           Elpi.API.PPX.readback_string ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__73 in
                         let (elpi__state, elpi__74, elpi__76) =
                           elpi_readback_ty ~depth:elpi__depth elpi__hyps
                             elpi__constraints elpi__state elpi__74 in
                         (elpi__state,
                           (elpi__78, (Entry (elpi__73, elpi__74))),
                           (List.concat [elpi__77; elpi__75; elpi__76]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_ctx_Entryc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_ctx_TEentryc ->
                    let (elpi__state, elpi__84, elpi__83) =
                      Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.readback
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__79::elpi__80::[] ->
                         let (elpi__state, elpi__79, elpi__81) =
                           Elpi.API.PPX.readback_string ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__79 in
                         let (elpi__state, elpi__80, elpi__82) =
                           Elpi.Builtin.PPX.readback_bool ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__80 in
                         (elpi__state,
                           (elpi__84, (TEentry (elpi__79, elpi__80))),
                           (List.concat [elpi__83; elpi__81; elpi__82]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_ctx_TEentryc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "ctx" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    let term : 'c . (term, #Ctx_for_term.t as 'c) Elpi.API.Conversion.t =
      let kind = Elpi.API.Conversion.TyName "term" in
      {
        Elpi.API.Conversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"term";
               (Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"app"
                  ~doc:"App"
                  ~args:[Elpi.API.Conversion.TyName elpi_constant_type_term;
                        Elpi.API.Conversion.TyName elpi_constant_type_term];
                Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tapp"
                  ~doc:"Tapp"
                  ~args:[Elpi.API.Conversion.TyName elpi_constant_type_term;
                        Elpi.API.Conversion.TyName elpi_constant_type_ty]);
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"lam"
                 ~doc:"Lam"
                 ~args:[Elpi.API.Conversion.TyName elpi_constant_type_ty;
                       Elpi.API.BuiltInData.string.Elpi.API.Conversion.ty;
                       Elpi.API.Conversion.TyApp
                         ("->", (Elpi.API.Conversion.TyName "term"),
                           [Elpi.API.Conversion.TyName
                              elpi_constant_type_term])]);
        pp = pp_term;
        embed = elpi_embed_term;
        readback = elpi_readback_term
      }
    let ty : 'c . (ty, #Ctx_for_ty.t as 'c) Elpi.API.Conversion.t =
      let kind = Elpi.API.Conversion.TyName "ty" in
      {
        Elpi.API.Conversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"ty";
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tidx"
                 ~doc:"TIdx"
                 ~args:[Elpi.API.Conversion.TyName elpi_constant_type_ty;
                       Elpi.API.Conversion.TyName elpi_constant_type_term];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"tabs"
                 ~doc:"TAbs"
                 ~args:[Elpi.API.BuiltInData.string.Elpi.API.Conversion.ty;
                       Elpi.Builtin.bool.Elpi.API.Conversion.ty;
                       Elpi.API.Conversion.TyApp
                         ("->", (Elpi.API.Conversion.TyName "ty"),
                           [Elpi.API.Conversion.TyName elpi_constant_type_ty])]);
        pp = pp_ty;
        embed = elpi_embed_ty;
        readback = elpi_readback_ty
      }
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
                 ~ty:(Elpi.API.Conversion.TyName "prop") ~name:"entry"
                 ~doc:"Entry"
                 ~args:[Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.ty;
                       Elpi.API.BuiltInData.string.Elpi.API.Conversion.ty;
                       Elpi.API.Conversion.TyName elpi_constant_type_ty];
               Elpi.API.PPX.Doc.constructor fmt
                 ~ty:(Elpi.API.Conversion.TyName "prop") ~name:"teentry"
                 ~doc:"TEentry"
                 ~args:[Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.ty;
                       Elpi.API.BuiltInData.string.Elpi.API.Conversion.ty;
                       Elpi.Builtin.bool.Elpi.API.Conversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_ctx fmt x);
        embed = elpi_embed_ctx;
        readback = elpi_readback_ctx
      }
    let elpi_term = Elpi.API.BuiltIn.MLData term
    let elpi_ty = Elpi.API.BuiltIn.MLData ty
    let elpi_ctx = Elpi.API.BuiltIn.MLData ctx
    class ctx_for_term (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_term.t =
      object (_)
        inherit  ((Elpi.API.Conversion.ctx) h)
        inherit ! ((ctx_for_ctx) h s)
        method ctx = context_made_of_ctx.Elpi.API.Conversion.get s
      end
    let (in_ctx_for_term : Ctx_for_term.t Elpi.API.Conversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_ctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_ctx ctx
                  h c s in
              (s, ((new ctx_for_term) h s), (List.concat [gls0]))
    class ctx_for_ty (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_ty.t =
      object (_)
        inherit  ((Elpi.API.Conversion.ctx) h)
        inherit ! ((ctx_for_ctx) h s)
        method ctx = context_made_of_ctx.Elpi.API.Conversion.get s
      end
    let (in_ctx_for_ty : Ctx_for_ty.t Elpi.API.Conversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_ctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_ctx ctx
                  h c s in
              (s, ((new ctx_for_ty) h s), (List.concat [gls0]))
    class ctx_for_ctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_ctx.t =
      object (_)
        inherit  ((Elpi.API.Conversion.ctx) h)
        inherit ! ((ctx_for_ctx) h s)
        method ctx = context_made_of_ctx.Elpi.API.Conversion.get s
      end
    let (in_ctx_for_ctx : Ctx_for_ctx.t Elpi.API.Conversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_ctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_ctx ctx
                  h c s in
              (s, ((new ctx_for_ctx) h s), (List.concat [gls0]))
    let () = declaration := ((!declaration) @ [elpi_term; elpi_ty; elpi_ctx])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
open Elpi.API
let in_ctx
  : ((tctx ContextualConversion.ctx_entry RawData.Constants.Map.t * ctx
       ContextualConversion.ctx_entry RawData.Constants.Map.t),
      Data.constraints) ContextualConversion.ctx_readback
  = in_ctx
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!declaration)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
