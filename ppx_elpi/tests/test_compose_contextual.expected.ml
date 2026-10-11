let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show = Format.asprintf "%a" pp
  end
type c1 =
  | E1 of ((string)[@elpi.key "t1"]) * bool [@@elpi.index (module String)]
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_c1
      : Ppx_deriving_runtime.Format.formatter ->
          c1 -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt ->
            function
            | E1 (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_compose_contextual.E1 (@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%B") a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_c1 : c1 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_c1 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_c1 = "c1"
    let elpi_constant_type_c1c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_c1
    let elpi_constant_constructor_c1_E1 = "e1"
    let elpi_constant_constructor_c1_E1c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_c1_E1
    module Elpi_c1_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_c1_state =
      Elpi.API.State.declare_component ~name:"c1"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_c1_Map.empty : Elpi.API.RawData.constant
                                         Elpi_c1_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : c1
                                                             Elpi.API.PPX.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x) ()
    let elpi_c1_to_key ~depth:_  elpi__fun_arg =
      match elpi__fun_arg with | E1 (elpi__16, _) -> elpi__16
    let elpi_is_c1 { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x } =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_c1_E1c)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Utils.type_error
                   "context entry applied to a non bound variable")
          else None
      | _ -> None
    let elpi_push_c1 ~depth:elpi__depth  elpi__state elpi__name
      elpi__ctx_item =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_c1_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_c1_Map.add elpi__name elpi__i elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item
          elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_c1_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    let elpi_pop_c1 ~depth:elpi__depth  elpi__state elpi__name =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_c1_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_c1_Map.remove elpi__name elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_c1_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    module Ctx_for_c1 =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_c1 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c1), 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | (elpi__9, E1 (elpi__7, elpi__8)) ->
                    let (elpi__state, elpi__13, elpi__10) =
                      (fun ~depth ->
                         fun elpi__hyps ->
                           fun elpi__constraints ->
                             fun elpi__state ->
                               fun elpi__i ->
                                 if elpi__i < 0
                                 then
                                   Elpi.API.Utils.type_error
                                     "not a bound variable";
                                 (elpi__state,
                                   (Elpi.API.RawData.mkConst elpi__i), []))
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__9 in
                    let (elpi__state, elpi__14, elpi__11) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
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
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_c1_E1c
                         [elpi__13; elpi__14; elpi__15]),
                      (List.concat [elpi__10; elpi__11; elpi__12]))
    and elpi_readback_c1 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c1), 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_c1_E1c ->
                    let (elpi__state, elpi__6, elpi__5) =
                      (fun ~depth ->
                         fun elpi__hyps ->
                           fun elpi__constraints ->
                             fun elpi__state ->
                               fun elpi__t ->
                                 match Elpi.API.RawData.look ~depth elpi__t
                                 with
                                 | Elpi.API.RawData.Const elpi__i when
                                     elpi__i >= 0 ->
                                     (elpi__state, elpi__i, [])
                                 | _ ->
                                     Elpi.API.Utils.type_error
                                       "not a bound variable")
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
                                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
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
                         (elpi__state, (elpi__6, (E1 (elpi__1, elpi__2))),
                           (List.concat [elpi__5; elpi__3; elpi__4]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_c1_E1c)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "c1" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and c1 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c1), 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "c1" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               ();
               Elpi.API.PPX.Doc.context_entry fmt ~name:"e1" ~doc:"E1"
                 ~key:(Elpi.API.ContextualConversion.TyName "t1")
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_c1 fmt x);
        embed = elpi_embed_c1;
        readback = elpi_readback_c1
      }
    let context_made_of_c1 =
      {
        Elpi.API.PPX.is_entry_for_bound_var = elpi_is_c1;
        to_key = elpi_c1_to_key;
        push = elpi_push_c1;
        pop = elpi_pop_c1;
        conv = c1;
        init =
          (fun state ->
             Elpi.API.State.set elpi_c1_state state
               ((Elpi_c1_Map.empty : Elpi.API.RawData.constant Elpi_c1_Map.t),
                 (Elpi.API.RawData.Constants.Map.empty : c1
                                                           Elpi.API.PPX.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get = (fun state -> snd @@ (Elpi.API.State.get elpi_c1_state state))
      }
    let elpi_c1 = Elpi.API.BuiltIn.MLDataC c1
    class ctx_for_c1 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_c1.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_c1 :
      (Ctx_for_c1.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_c1) h s), c, (List.concat []))
    let () = Elpi.API.PPX.add_declarations declaration [elpi_c1]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type t1 =
  | V1 of string [@elpi.var c1]
  | A1 of t1 * t1 
  | L1 of bool * string *
  ((t1)[@elpi.binder "t1" c1 (fun b -> fun s -> E1 (s, b))]) [@@deriving
                                                               (show,
                                                                 (elpi
                                                                    {
                                                                    declaration
                                                                    }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_t1
      : Ppx_deriving_runtime.Format.formatter ->
          t1 -> Ppx_deriving_runtime.unit
      =
      ((let __2 = pp_t1
        and __1 = pp_t1
        and __0 = pp_t1 in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              function
              | V1 a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_compose_contextual.V1@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])")
              | A1 (a0, a1) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_compose_contextual.A1 (@,";
                   ((__0 fmt) a0;
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__1 fmt) a1);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
              | L1 (a0, a1, a2) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_compose_contextual.L1 (@,";
                   (((Ppx_deriving_runtime.Format.fprintf fmt "%B") a0;
                     Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                     (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__2 fmt) a2);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_t1 : t1 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_t1 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_t1 = "t1"
    let elpi_constant_type_t1c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_t1
    let elpi_constant_constructor_t1_V1 = "v1"
    let elpi_constant_constructor_t1_V1c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t1_V1
    let elpi_constant_constructor_t1_A1 = "a1"
    let elpi_constant_constructor_t1_A1c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t1_A1
    let elpi_constant_constructor_t1_L1 = "l1"
    let elpi_constant_constructor_t1_L1c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t1_L1
    module Ctx_for_t1 =
      struct
        class type t =
          object
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_c1.t
            method  c1 : c1 Elpi.API.PPX.ctx_field
          end
      end
    let rec elpi_embed_t1 :
      'c 'csts .
        (t1, #Ctx_for_t1.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | V1 elpi__29 ->
                    let (elpi__ctx2dbl, _) =
                      Elpi.API.State.get elpi_c1_state elpi__state in
                    let elpi__key = (fun x -> x) elpi__29 in
                    (if not (Elpi_c1_Map.mem elpi__key elpi__ctx2dbl)
                     then Elpi.API.Utils.error "Unbound variable";
                     (elpi__state,
                       (Elpi.API.RawData.mkBound
                          (Elpi_c1_Map.find elpi__key elpi__ctx2dbl)), []))
                | A1 (elpi__32, elpi__33) ->
                    let (elpi__state, elpi__36, elpi__34) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_t1 ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__32 in
                    let (elpi__state, elpi__37, elpi__35) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_t1 ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__33 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_t1_A1c
                         [elpi__36; elpi__37]),
                      (List.concat [elpi__34; elpi__35]))
                | L1 (elpi__38, elpi__39, elpi__40) ->
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
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__39 in
                    let elpi__ctx_entry =
                      (fun b -> fun s -> E1 (s, b)) elpi__38 elpi__39 in
                    let elpi__ctx_key =
                      elpi_c1_to_key ~depth:elpi__depth elpi__ctx_entry in
                    let elpi__ctx_entry =
                      {
                        Elpi.API.PPX.entry = elpi__ctx_entry;
                        depth = elpi__depth
                      } in
                    let elpi__state =
                      elpi_push_c1 ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key elpi__ctx_entry in
                    let (elpi__state, elpi__47, elpi__43) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_t1 ~depth h c s t)
                        ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                        elpi__state elpi__40 in
                    let elpi__46 = Elpi.API.RawData.mkLam elpi__47 in
                    let elpi__state =
                      elpi_pop_c1 ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_t1_L1c
                         [elpi__44; elpi__45; elpi__46]),
                      (List.concat [elpi__41; elpi__42; elpi__43]))
    and elpi_readback_t1 :
      'c 'csts .
        (t1, #Ctx_for_t1.t as 'c, 'csts)
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
                      Elpi.API.State.get elpi_c1_state elpi__state in
                    (if
                       not
                         (Elpi.API.RawData.Constants.Map.mem elpi__hd
                            elpi__dbl2ctx)
                     then
                       Elpi.API.Utils.error
                         (Format.asprintf "Unbound variable: %s in %a"
                            (Elpi.API.RawData.Constants.show elpi__hd)
                            (Elpi.API.RawData.Constants.Map.pp
                               (Elpi.API.PPX.pp_ctx_entry pp_c1))
                            elpi__dbl2ctx);
                     (let { Elpi.API.PPX.entry = elpi__entry;
                            depth = elpi__depth }
                        =
                        Elpi.API.RawData.Constants.Map.find elpi__hd
                          elpi__dbl2ctx in
                      (elpi__state,
                        (V1 (elpi_c1_to_key ~depth:elpi__depth elpi__entry)),
                        [])))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_t1_A1c ->
                    let (elpi__state, elpi__22, elpi__21) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t -> elpi_readback_t1 ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__19::[] ->
                         let (elpi__state, elpi__19, elpi__20) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t -> elpi_readback_t1 ~depth h c s t)
                             ~depth:elpi__depth elpi__hyps elpi__constraints
                             elpi__state elpi__19 in
                         (elpi__state, (A1 (elpi__22, elpi__19)),
                           (List.concat [elpi__21; elpi__20]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_t1_A1c)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_t1_L1c ->
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
                                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__23 in
                         let elpi__ctx_entry =
                           (fun b -> fun s -> E1 (s, b)) elpi__28 elpi__23 in
                         let elpi__ctx_key =
                           elpi_c1_to_key ~depth:elpi__depth elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi.API.PPX.entry = elpi__ctx_entry;
                             depth = elpi__depth
                           } in
                         let elpi__state =
                           elpi_push_c1 ~depth:elpi__depth elpi__state
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
                                           elpi_readback_t1 ~depth h c s t))
                                 ~depth:(elpi__depth + 1) elpi__hyps
                                 elpi__constraints elpi__state elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_c1 ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state, (L1 (elpi__28, elpi__23, elpi__24)),
                           (List.concat [elpi__27; elpi__25; elpi__26]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_t1_L1c)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "t1" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and t1 :
      'c 'csts .
        (t1, #Ctx_for_t1.t as 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "t1" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
                 ~ty:kind ~name:"a1" ~doc:"A1"
                 ~args:[Elpi.API.ContextualConversion.TyName
                          elpi_constant_type_t1;
                       Elpi.API.ContextualConversion.TyName
                         elpi_constant_type_t1];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
                 ~ty:kind ~name:"l1" ~doc:"L1"
                 ~args:[Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty;
                       Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("->", (Elpi.API.ContextualConversion.TyName "t1"),
                           [Elpi.API.ContextualConversion.TyName
                              elpi_constant_type_t1])]);
        pp = pp_t1;
        embed = elpi_embed_t1;
        readback = elpi_readback_t1
      }
    let elpi_t1 = Elpi.API.BuiltIn.MLDataC t1
    let elpi__t1__deep_copy =
      "func t1.copy t1 -> t1.\nt1.copy (a1 A0 A1) (a1 B0 B1) :- (t1.copy A0 B0), (t1.copy A1 B1).\nt1.copy (l1 A0 A1 A2) (l1 B0 B1 B2) :- (bool.copy A0 B0), (string.copy A1 B1), (pi x\\ e1 x B1 B0 ==> t1.copy x x ==> (t1.copy (A2 x) (B2 x))).\n\n"
    class ctx_for_t1 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_t1.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_c1) h s)
        method c1 = context_made_of_c1.Elpi.API.PPX.get s
      end
    let (in_ctx_for_t1 :
      (Ctx_for_t1.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_c1) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_c1 ctx h
                  c s in
              (s, ((new ctx_for_t1) h s), c, (List.concat [gls0]))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_t1; Elpi.API.BuiltIn.LPCode elpi__t1__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let t1 : 'c 'csts . (t1, #ctx_for_t1 as 'c, 'csts) ContextualConversion.t =
  t1
type c2 =
  | E2 of ((string)[@elpi.key "t2"]) * int [@@elpi.index (module String)]
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_c2
      : Ppx_deriving_runtime.Format.formatter ->
          c2 -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt ->
            function
            | E2 (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_compose_contextual.E2 (@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%d") a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_c2 : c2 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_c2 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_c2 = "c2"
    let elpi_constant_type_c2c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_c2
    let elpi_constant_constructor_c2_E2 = "e2"
    let elpi_constant_constructor_c2_E2c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_c2_E2
    module Elpi_c2_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_c2_state =
      Elpi.API.State.declare_component ~name:"c2"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_c2_Map.empty : Elpi.API.RawData.constant
                                         Elpi_c2_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : c2
                                                             Elpi.API.PPX.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x) ()
    let elpi_c2_to_key ~depth:_  elpi__fun_arg =
      match elpi__fun_arg with | E2 (elpi__63, _) -> elpi__63
    let elpi_is_c2 { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x } =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_c2_E2c)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Utils.type_error
                   "context entry applied to a non bound variable")
          else None
      | _ -> None
    let elpi_push_c2 ~depth:elpi__depth  elpi__state elpi__name
      elpi__ctx_item =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_c2_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_c2_Map.add elpi__name elpi__i elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item
          elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_c2_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    let elpi_pop_c2 ~depth:elpi__depth  elpi__state elpi__name =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_c2_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_c2_Map.remove elpi__name elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_c2_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    module Ctx_for_c2 =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_c2 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c2), 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | (elpi__56, E2 (elpi__54, elpi__55)) ->
                    let (elpi__state, elpi__60, elpi__57) =
                      (fun ~depth ->
                         fun elpi__hyps ->
                           fun elpi__constraints ->
                             fun elpi__state ->
                               fun elpi__i ->
                                 if elpi__i < 0
                                 then
                                   Elpi.API.Utils.type_error
                                     "not a bound variable";
                                 (elpi__state,
                                   (Elpi.API.RawData.mkConst elpi__i), []))
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__56 in
                    let (elpi__state, elpi__61, elpi__58) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__54 in
                    let (elpi__state, elpi__62, elpi__59) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__55 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_c2_E2c
                         [elpi__60; elpi__61; elpi__62]),
                      (List.concat [elpi__57; elpi__58; elpi__59]))
    and elpi_readback_c2 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c2), 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_c2_E2c ->
                    let (elpi__state, elpi__53, elpi__52) =
                      (fun ~depth ->
                         fun elpi__hyps ->
                           fun elpi__constraints ->
                             fun elpi__state ->
                               fun elpi__t ->
                                 match Elpi.API.RawData.look ~depth elpi__t
                                 with
                                 | Elpi.API.RawData.Const elpi__i when
                                     elpi__i >= 0 ->
                                     (elpi__state, elpi__i, [])
                                 | _ ->
                                     Elpi.API.Utils.type_error
                                       "not a bound variable")
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
                                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__48 in
                         let (elpi__state, elpi__49, elpi__51) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__49 in
                         (elpi__state, (elpi__53, (E2 (elpi__48, elpi__49))),
                           (List.concat [elpi__52; elpi__50; elpi__51]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_c2_E2c)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "c2" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and c2 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c2), 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "c2" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               ();
               Elpi.API.PPX.Doc.context_entry fmt ~name:"e2" ~doc:"E2"
                 ~key:(Elpi.API.ContextualConversion.TyName "t2")
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_c2 fmt x);
        embed = elpi_embed_c2;
        readback = elpi_readback_c2
      }
    let context_made_of_c2 =
      {
        Elpi.API.PPX.is_entry_for_bound_var = elpi_is_c2;
        to_key = elpi_c2_to_key;
        push = elpi_push_c2;
        pop = elpi_pop_c2;
        conv = c2;
        init =
          (fun state ->
             Elpi.API.State.set elpi_c2_state state
               ((Elpi_c2_Map.empty : Elpi.API.RawData.constant Elpi_c2_Map.t),
                 (Elpi.API.RawData.Constants.Map.empty : c2
                                                           Elpi.API.PPX.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get = (fun state -> snd @@ (Elpi.API.State.get elpi_c2_state state))
      }
    let elpi_c2 = Elpi.API.BuiltIn.MLDataC c2
    class ctx_for_c2 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_c2.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_c2 :
      (Ctx_for_c2.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_c2) h s), c, (List.concat []))
    let () = Elpi.API.PPX.add_declarations declaration [elpi_c2]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type t2 =
  | V2 of string [@elpi.var c2]
  | A2 of t2 * t2 
  | L2 of int * string *
  ((t2)[@elpi.binder "t2" c2 (fun i -> fun s -> E2 (s, i))]) [@@deriving
                                                               (show,
                                                                 (elpi
                                                                    {
                                                                    declaration
                                                                    }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_t2
      : Ppx_deriving_runtime.Format.formatter ->
          t2 -> Ppx_deriving_runtime.unit
      =
      ((let __2 = pp_t2
        and __1 = pp_t2
        and __0 = pp_t2 in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              function
              | V2 a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_compose_contextual.V2@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])")
              | A2 (a0, a1) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_compose_contextual.A2 (@,";
                   ((__0 fmt) a0;
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__1 fmt) a1);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
              | L2 (a0, a1, a2) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_compose_contextual.L2 (@,";
                   (((Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                     Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                     (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__2 fmt) a2);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_t2 : t2 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_t2 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_t2 = "t2"
    let elpi_constant_type_t2c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_t2
    let elpi_constant_constructor_t2_V2 = "v2"
    let elpi_constant_constructor_t2_V2c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t2_V2
    let elpi_constant_constructor_t2_A2 = "a2"
    let elpi_constant_constructor_t2_A2c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t2_A2
    let elpi_constant_constructor_t2_L2 = "l2"
    let elpi_constant_constructor_t2_L2c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t2_L2
    module Ctx_for_t2 =
      struct
        class type t =
          object
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_c2.t
            method  c2 : c2 Elpi.API.PPX.ctx_field
          end
      end
    let rec elpi_embed_t2 :
      'c 'csts .
        (t2, #Ctx_for_t2.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | V2 elpi__76 ->
                    let (elpi__ctx2dbl, _) =
                      Elpi.API.State.get elpi_c2_state elpi__state in
                    let elpi__key = (fun x -> x) elpi__76 in
                    (if not (Elpi_c2_Map.mem elpi__key elpi__ctx2dbl)
                     then Elpi.API.Utils.error "Unbound variable";
                     (elpi__state,
                       (Elpi.API.RawData.mkBound
                          (Elpi_c2_Map.find elpi__key elpi__ctx2dbl)), []))
                | A2 (elpi__79, elpi__80) ->
                    let (elpi__state, elpi__83, elpi__81) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_t2 ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__79 in
                    let (elpi__state, elpi__84, elpi__82) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_t2 ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__80 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_t2_A2c
                         [elpi__83; elpi__84]),
                      (List.concat [elpi__81; elpi__82]))
                | L2 (elpi__85, elpi__86, elpi__87) ->
                    let (elpi__state, elpi__91, elpi__88) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__85 in
                    let (elpi__state, elpi__92, elpi__89) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__86 in
                    let elpi__ctx_entry =
                      (fun i -> fun s -> E2 (s, i)) elpi__85 elpi__86 in
                    let elpi__ctx_key =
                      elpi_c2_to_key ~depth:elpi__depth elpi__ctx_entry in
                    let elpi__ctx_entry =
                      {
                        Elpi.API.PPX.entry = elpi__ctx_entry;
                        depth = elpi__depth
                      } in
                    let elpi__state =
                      elpi_push_c2 ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key elpi__ctx_entry in
                    let (elpi__state, elpi__94, elpi__90) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_t2 ~depth h c s t)
                        ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                        elpi__state elpi__87 in
                    let elpi__93 = Elpi.API.RawData.mkLam elpi__94 in
                    let elpi__state =
                      elpi_pop_c2 ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_t2_L2c
                         [elpi__91; elpi__92; elpi__93]),
                      (List.concat [elpi__88; elpi__89; elpi__90]))
    and elpi_readback_t2 :
      'c 'csts .
        (t2, #Ctx_for_t2.t as 'c, 'csts)
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
                      Elpi.API.State.get elpi_c2_state elpi__state in
                    (if
                       not
                         (Elpi.API.RawData.Constants.Map.mem elpi__hd
                            elpi__dbl2ctx)
                     then
                       Elpi.API.Utils.error
                         (Format.asprintf "Unbound variable: %s in %a"
                            (Elpi.API.RawData.Constants.show elpi__hd)
                            (Elpi.API.RawData.Constants.Map.pp
                               (Elpi.API.PPX.pp_ctx_entry pp_c2))
                            elpi__dbl2ctx);
                     (let { Elpi.API.PPX.entry = elpi__entry;
                            depth = elpi__depth }
                        =
                        Elpi.API.RawData.Constants.Map.find elpi__hd
                          elpi__dbl2ctx in
                      (elpi__state,
                        (V2 (elpi_c2_to_key ~depth:elpi__depth elpi__entry)),
                        [])))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_t2_A2c ->
                    let (elpi__state, elpi__69, elpi__68) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t -> elpi_readback_t2 ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__66::[] ->
                         let (elpi__state, elpi__66, elpi__67) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t -> elpi_readback_t2 ~depth h c s t)
                             ~depth:elpi__depth elpi__hyps elpi__constraints
                             elpi__state elpi__66 in
                         (elpi__state, (A2 (elpi__69, elpi__66)),
                           (List.concat [elpi__68; elpi__67]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_t2_A2c)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_t2_L2c ->
                    let (elpi__state, elpi__75, elpi__74) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
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
                                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__70 in
                         let elpi__ctx_entry =
                           (fun i -> fun s -> E2 (s, i)) elpi__75 elpi__70 in
                         let elpi__ctx_key =
                           elpi_c2_to_key ~depth:elpi__depth elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi.API.PPX.entry = elpi__ctx_entry;
                             depth = elpi__depth
                           } in
                         let elpi__state =
                           elpi_push_c2 ~depth:elpi__depth elpi__state
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
                                           elpi_readback_t2 ~depth h c s t))
                                 ~depth:(elpi__depth + 1) elpi__hyps
                                 elpi__constraints elpi__state elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_c2 ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state, (L2 (elpi__75, elpi__70, elpi__71)),
                           (List.concat [elpi__74; elpi__72; elpi__73]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_t2_L2c)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "t2" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and t2 :
      'c 'csts .
        (t2, #Ctx_for_t2.t as 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "t2" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
                 ~ty:kind ~name:"a2" ~doc:"A2"
                 ~args:[Elpi.API.ContextualConversion.TyName
                          elpi_constant_type_t2;
                       Elpi.API.ContextualConversion.TyName
                         elpi_constant_type_t2];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
                 ~ty:kind ~name:"l2" ~doc:"L2"
                 ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                       Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("->", (Elpi.API.ContextualConversion.TyName "t2"),
                           [Elpi.API.ContextualConversion.TyName
                              elpi_constant_type_t2])]);
        pp = pp_t2;
        embed = elpi_embed_t2;
        readback = elpi_readback_t2
      }
    let elpi_t2 = Elpi.API.BuiltIn.MLDataC t2
    let elpi__t2__deep_copy =
      "func t2.copy t2 -> t2.\nt2.copy (a2 A0 A1) (a2 B0 B1) :- (t2.copy A0 B0), (t2.copy A1 B1).\nt2.copy (l2 A0 A1 A2) (l2 B0 B1 B2) :- (int.copy A0 B0), (string.copy A1 B1), (pi x\\ e2 x B1 B0 ==> t2.copy x x ==> (t2.copy (A2 x) (B2 x))).\n\n"
    class ctx_for_t2 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_t2.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_c2) h s)
        method c2 = context_made_of_c2.Elpi.API.PPX.get s
      end
    let (in_ctx_for_t2 :
      (Ctx_for_t2.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_c2) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_c2 ctx h
                  c s in
              (s, ((new ctx_for_t2) h s), c, (List.concat [gls0]))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_t2; Elpi.API.BuiltIn.LPCode elpi__t2__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let t2 : 'c 'csts . (t2, #ctx_for_t2 as 'c, 'csts) ContextualConversion.t =
  t2
include
  struct
    class ctx_for_both (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state) =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_t1) h s)
        inherit ! ((ctx_for_t2) h s)
      end
    let (in_ctx_for_both :
      (ctx_for_both, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let (s, _, c, gls0) = in_ctx_for_t1 ~depth h c s in
              let (s, _, c, gls1) = in_ctx_for_t2 ~depth h c s in
              (s, ((new ctx_for_both) h s), c, (List.concat [gls0; gls1]))
  end
open BuiltInPredicate.Notation
let both_to_string =
  BuiltInPredicate.ContextualPred
    ("t1->t2->string", in_ctx_for_both,
      (In
         (t1, "A",
           (In
              (t2, "B",
                (Out
                   (BuiltInData.stringC, "S",
                     (Read "a t1 and a t2, each one under its own context"))))))),
      (fun (a : t1) ->
         fun (b : t2) ->
           fun (_s : string BuiltInPredicate.oarg) ->
             fun ~depth:_ ->
               fun c ->
                 fun (_cst : Data.constraints) ->
                   fun (_state : State.t) ->
                     !:
                       (Format.asprintf
                          "@[<hov>%a@ |-@ %a@ ;@ %a@ |-@ %a@]@\n%!"
                          (RawData.Constants.Map.pp (PPX.pp_ctx_entry pp_c1))
                          c#c1 t1.pp a
                          (RawData.Constants.Map.pp (PPX.pp_ctx_entry pp_c2))
                          c#c2 t2.pp b)))
let builtin =
  let open BuiltIn in
    BuiltIn.declare ~file_name
      ((PPX.to_list declaration) @ [MLCode (both_to_string, DocAbove)])
let program =
  {|
main :-
  pi x\ pi y\
    e1 x "x" tt ==>
    e2 y "y" 1 ==>
    % the bound variables are copied to themselves
    t1.copy x x ==> t2.copy y y ==> (
      sigma A B C D\
        A = (l1 tt "z" z\ a1 z x),
        B = (a2 y y),
        print {t1->t2->string A B},
        t1.copy A C,
        t2.copy B D,
        print {t1->t2->string C D}).
|}
let () = Ppx_tests_lib.run_program builtin program
