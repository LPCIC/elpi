let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show x = x
  end
type tctx =
  | TDecl of ((string)[@elpi.key "tye"]) * bool [@@elpi.index
                                                  (module String)][@@deriving
                                                                    (show,
                                                                    (elpi
                                                                    {
                                                                    declaration
                                                                    }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_tctx
      : Ppx_deriving_runtime.Format.formatter ->
          tctx -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt ->
            function
            | TDecl (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_two_layers_context.TDecl (@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%B") a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_tctx : tctx -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_tctx x[@@ocaml.warning
                                                                    "-32"]
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
      Elpi.API.State.declare_component ~name:"tctx"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_tctx_Map.empty : Elpi.API.RawData.constant
                                           Elpi_tctx_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : tctx
                                                             Elpi.API.PPX.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x) ()
    let elpi_tctx_to_key ~depth:_  elpi__fun_arg =
      match elpi__fun_arg with | TDecl (elpi__16, _) -> elpi__16
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
                   "context entry applied to a non bound variable")
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
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | (elpi__9, TDecl (elpi__7, elpi__8)) ->
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
                         elpi_constant_constructor_tctx_TDeclc
                         [elpi__13; elpi__14; elpi__15]),
                      (List.concat [elpi__10; elpi__11; elpi__12]))
    and elpi_readback_tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), 'c, 'csts)
          Elpi.API.ContextualConversion.readback
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
    and tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "tctx" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               ();
               Elpi.API.PPX.Doc.context_entry fmt ~name:"tdecl" ~doc:"TDecl"
                 ~key:(Elpi.API.ContextualConversion.TyName "tye")
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_tctx fmt x);
        embed = elpi_embed_tctx;
        readback = elpi_readback_tctx
      }
    let context_made_of_tctx =
      {
        Elpi.API.PPX.is_entry_for_bound_var = elpi_is_tctx;
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
                                                           Elpi.API.PPX.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get =
          (fun state -> snd @@ (Elpi.API.State.get elpi_tctx_state state))
      }
    let elpi_tctx = Elpi.API.BuiltIn.MLDataC tctx
    class ctx_for_tctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tctx.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_tctx :
      (Ctx_for_tctx.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_tctx) h s), c, (List.concat []))
    let () = Elpi.API.PPX.add_declarations declaration [elpi_tctx]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type tye =
  | TVar of string [@elpi.var tctx]
  | TConst of string 
  | TArrow of tye * tye [@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_tye
      : Ppx_deriving_runtime.Format.formatter ->
          tye -> Ppx_deriving_runtime.unit
      =
      ((let __1 = pp_tye
        and __0 = pp_tye in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              function
              | TVar a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_two_layers_context.TVar@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])")
              | TConst a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_two_layers_context.TConst@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])")
              | TArrow (a0, a1) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_two_layers_context.TArrow (@,";
                   ((__0 fmt) a0;
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__1 fmt) a1);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_tye : tye -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_tye x[@@ocaml.warning
                                                                   "-32"]
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
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi.API.PPX.ctx_field
          end
      end
    let rec elpi_embed_tye :
      'c 'csts .
        (tye, #Ctx_for_tye.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
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
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__28 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_tye_TConstc [elpi__30]),
                      (List.concat [elpi__29]))
                | TArrow (elpi__31, elpi__32) ->
                    let (elpi__state, elpi__35, elpi__33) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_tye ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__31 in
                    let (elpi__state, elpi__36, elpi__34) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_tye ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__32 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_tye_TArrowc
                         [elpi__35; elpi__36]),
                      (List.concat [elpi__33; elpi__34]))
    and elpi_readback_tye :
      'c 'csts .
        (tye, #Ctx_for_tye.t as 'c, 'csts)
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
                               (Elpi.API.PPX.pp_ctx_entry pp_tctx))
                            elpi__dbl2ctx);
                     (let { Elpi.API.PPX.entry = elpi__entry;
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
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
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
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t -> elpi_readback_tye ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__21::[] ->
                         let (elpi__state, elpi__21, elpi__22) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t -> elpi_readback_tye ~depth h c s t)
                             ~depth:elpi__depth elpi__hyps elpi__constraints
                             elpi__state elpi__21 in
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
    and tye :
      'c 'csts .
        (tye, #Ctx_for_tye.t as 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "tye" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:6 ~variant:0
                 ~ty:kind ~name:"tconst" ~doc:"TConst"
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:6 ~variant:0
                 ~ty:kind ~name:"tarrow" ~doc:"TArrow"
                 ~args:[Elpi.API.ContextualConversion.TyName
                          elpi_constant_type_tye;
                       Elpi.API.ContextualConversion.TyName
                         elpi_constant_type_tye]);
        pp = pp_tye;
        embed = elpi_embed_tye;
        readback = elpi_readback_tye
      }
    let elpi_tye = Elpi.API.BuiltIn.MLDataC tye
    let elpi__tye__deep_copy =
      "func tye.copy tye -> tye.\ntye.copy (tconst A0) (tconst B0) :- (string.copy A0 B0).\ntye.copy (tarrow A0 A1) (tarrow B0 B1) :- (tye.copy A0 B0), (tye.copy A1 B1).\n\n"
    class ctx_for_tye (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tye.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx = context_made_of_tctx.Elpi.API.PPX.get s
      end
    let (in_ctx_for_tye :
      (Ctx_for_tye.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_tctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tctx ctx
                  h c s in
              (s, ((new ctx_for_tye) h s), c, (List.concat [gls0]))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_tye; Elpi.API.BuiltIn.LPCode elpi__tye__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let tye : 'a 'csts . (tye, #ctx_for_tye as 'a, 'csts) ContextualConversion.t
  = tye
type ty =
  | Mono of tye 
  | Forall of string * bool *
  ((ty)[@elpi.binder "tye" tctx (fun s -> fun b -> TDecl (s, b))]) [@@deriving
                                                                    (show,
                                                                    (elpi
                                                                    {
                                                                    declaration
                                                                    }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_ty
      : Ppx_deriving_runtime.Format.formatter ->
          ty -> Ppx_deriving_runtime.unit
      =
      ((let __1 = pp_ty
        and __0 = pp_tye in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              function
              | Mono a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_two_layers_context.Mono@ ";
                   (__0 fmt) a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])")
              | Forall (a0, a1, a2) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_two_layers_context.Forall (@,";
                   (((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                     Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                     (Ppx_deriving_runtime.Format.fprintf fmt "%B") a1);
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__1 fmt) a2);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_ty : ty -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_ty x[@@ocaml.warning
                                                                  "-32"]
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
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi.API.PPX.ctx_field
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
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | Mono elpi__45 ->
                    let (elpi__state, elpi__47, elpi__46) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 tye.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__45 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_ty_Monoc [elpi__47]),
                      (List.concat [elpi__46]))
                | Forall (elpi__48, elpi__49, elpi__50) ->
                    let (elpi__state, elpi__54, elpi__51) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__48 in
                    let (elpi__state, elpi__55, elpi__52) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__49 in
                    let elpi__ctx_entry =
                      (fun s -> fun b -> TDecl (s, b)) elpi__48 elpi__49 in
                    let elpi__ctx_key =
                      elpi_tctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                    let elpi__ctx_entry =
                      {
                        Elpi.API.PPX.entry = elpi__ctx_entry;
                        depth = elpi__depth
                      } in
                    let elpi__state =
                      elpi_push_tctx ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key elpi__ctx_entry in
                    let (elpi__state, elpi__57, elpi__53) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_ty ~depth h c s t)
                        ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                        elpi__state elpi__50 in
                    let elpi__56 = Elpi.API.RawData.mkLam elpi__57 in
                    let elpi__state =
                      elpi_pop_tctx ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_ty_Forallc
                         [elpi__54; elpi__55; elpi__56]),
                      (List.concat [elpi__51; elpi__52; elpi__53]))
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
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_ty_Monoc ->
                    let (elpi__state, elpi__38, elpi__37) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 tye.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
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
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__39::elpi__40::[] ->
                         let (elpi__state, elpi__39, elpi__41) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__39 in
                         let elpi__ctx_entry =
                           (fun s -> fun b -> TDecl (s, b)) elpi__44 elpi__39 in
                         let elpi__ctx_key =
                           elpi_tctx_to_key ~depth:elpi__depth
                             elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi.API.PPX.entry = elpi__ctx_entry;
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
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:6 ~variant:0
                 ~ty:kind ~name:"mono" ~doc:"Mono"
                 ~args:[tye.Elpi.API.ContextualConversion.ty];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:6 ~variant:0
                 ~ty:kind ~name:"forall" ~doc:"Forall"
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("->", (Elpi.API.ContextualConversion.TyName "tye"),
                           [Elpi.API.ContextualConversion.TyName
                              elpi_constant_type_ty])]);
        pp = pp_ty;
        embed = elpi_embed_ty;
        readback = elpi_readback_ty
      }
    let elpi_ty = Elpi.API.BuiltIn.MLDataC ty
    let elpi__ty__deep_copy =
      "func ty.copy ty -> ty.\nty.copy (mono A0) (mono B0) :- (tye.copy A0 B0).\nty.copy (forall A0 A1 A2) (forall B0 B1 B2) :- (string.copy A0 B0), (bool.copy A1 B1), (pi x\\ tdecl x B0 B1 ==> tye.copy x x ==> (ty.copy (A2 x) (B2 x))).\n\n"
    class ctx_for_ty (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_ty.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx = context_made_of_tctx.Elpi.API.PPX.get s
      end
    let (in_ctx_for_ty :
      (Ctx_for_ty.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_tctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tctx ctx
                  h c s in
              (s, ((new ctx_for_ty) h s), c, (List.concat [gls0]))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_ty; Elpi.API.BuiltIn.LPCode elpi__ty__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let ty : 'a 'csts . (ty, #ctx_for_ty as 'a, 'csts) ContextualConversion.t =
  ty
type ctx =
  | Decl of ((string)[@elpi.key "term"]) * ty [@@elpi.index (module String)]
[@@deriving (show, (elpi { declaration; context = [tctx] }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_ctx
      : Ppx_deriving_runtime.Format.formatter ->
          ctx -> Ppx_deriving_runtime.unit
      =
      ((let __0 = pp_ty in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              function
              | Decl (a0, a1) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_two_layers_context.Decl (@,";
                   ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__0 fmt) a1);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_ctx : ctx -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_ctx x[@@ocaml.warning
                                                                   "-32"]
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
      Elpi.API.State.declare_component ~name:"ctx"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_ctx_Map.empty : Elpi.API.RawData.constant
                                          Elpi_ctx_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : ctx
                                                             Elpi.API.PPX.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x) ()
    let elpi_ctx_to_key ~depth:_  elpi__fun_arg =
      match elpi__fun_arg with | Decl (elpi__73, _) -> elpi__73
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
                   "context entry applied to a non bound variable")
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
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi.API.PPX.ctx_field
          end
      end
    let rec elpi_embed_ctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * ctx), #Ctx_for_ctx.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | (elpi__66, Decl (elpi__64, elpi__65)) ->
                    let (elpi__state, elpi__70, elpi__67) =
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
                        elpi__state elpi__66 in
                    let (elpi__state, elpi__71, elpi__68) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__64 in
                    let (elpi__state, elpi__72, elpi__69) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 ty.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__65 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_ctx_Declc
                         [elpi__70; elpi__71; elpi__72]),
                      (List.concat [elpi__67; elpi__68; elpi__69]))
    and elpi_readback_ctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * ctx), #Ctx_for_ctx.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback
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
                     | elpi__58::elpi__59::[] ->
                         let (elpi__state, elpi__58, elpi__60) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__58 in
                         let (elpi__state, elpi__59, elpi__61) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      ty.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
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
    and ctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * ctx), #Ctx_for_ctx.t as 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "ctx" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               ();
               Elpi.API.PPX.Doc.context_entry fmt ~name:"decl" ~doc:"Decl"
                 ~key:(Elpi.API.ContextualConversion.TyName "term")
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       ty.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_ctx fmt x);
        embed = elpi_embed_ctx;
        readback = elpi_readback_ctx
      }
    let context_made_of_ctx =
      {
        Elpi.API.PPX.is_entry_for_bound_var = elpi_is_ctx;
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
                                                           Elpi.API.PPX.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get = (fun state -> snd @@ (Elpi.API.State.get elpi_ctx_state state))
      }
    let elpi_ctx = Elpi.API.BuiltIn.MLDataC ctx
    class ctx_for_ctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_ctx.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx = context_made_of_tctx.Elpi.API.PPX.get s
      end
    let (in_ctx_for_ctx :
      (Ctx_for_ctx.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_tctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tctx ctx
                  h c s in
              (s, ((new ctx_for_ctx) h s), c, (List.concat [gls0]))
    let () = Elpi.API.PPX.add_declarations declaration [elpi_ctx]
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
                                                   {
                                                     declaration;
                                                     context = [tctx; ctx]
                                                   }][@@elpi.pp
                                                       let rec aux fmt =
                                                         function
                                                         | Var s ->
                                                             Format.fprintf
                                                               fmt "%s" s
                                                         | App tl ->
                                                             Format.fprintf
                                                               fmt "App %a"
                                                               (RawPp.list
                                                                  aux " ") tl
                                                         | Lam (s, ty, t) ->
                                                             Format.fprintf
                                                               fmt
                                                               "Lam %s (%a)"
                                                               s aux t
                                                         | Literal i ->
                                                             Format.fprintf
                                                               fmt "%d" i
                                                         | Cast (t, _) ->
                                                             aux fmt t in
                                                       aux]
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
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi.API.PPX.ctx_field
            inherit Ctx_for_ctx.t
            method  ctx : ctx Elpi.API.PPX.ctx_field
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
              fun elpi__fun_arg ->
                match elpi__fun_arg with
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
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 (let embed = elpi_embed_term in
                                  fun ~depth ->
                                    fun h ->
                                      fun c ->
                                        fun s ->
                                          fun l ->
                                            let (s, l, eg) =
                                              Elpi.API.Utils.map_acc
                                                (embed ~depth h c) s l in
                                            (s,
                                              (Elpi.API.Utils.list_to_lp_list
                                                 l), eg)) ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__91 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_term_Appc [elpi__93]),
                      (List.concat [elpi__92]))
                | Lam (elpi__94, elpi__95, elpi__96) ->
                    let (elpi__state, elpi__100, elpi__97) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__94 in
                    let (elpi__state, elpi__101, elpi__98) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 ty.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__95 in
                    let elpi__ctx_entry =
                      (fun s -> fun ty -> Decl (s, ty)) elpi__94 elpi__95 in
                    let elpi__ctx_key =
                      elpi_ctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                    let elpi__ctx_entry =
                      {
                        Elpi.API.PPX.entry = elpi__ctx_entry;
                        depth = elpi__depth
                      } in
                    let elpi__state =
                      elpi_push_ctx ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key elpi__ctx_entry in
                    let (elpi__state, elpi__103, elpi__99) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_term ~depth h c s t)
                        ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                        elpi__state elpi__96 in
                    let elpi__102 = Elpi.API.RawData.mkLam elpi__103 in
                    let elpi__state =
                      elpi_pop_ctx ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
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
                                    default ~depth hyps constraints state a1
                                      a2))
                      (fun ~depth:elpi__depth ->
                         fun elpi__hyps ->
                           fun elpi__constraints ->
                             fun elpi__state ->
                               fun elpi__104 ->
                                 fun elpi__105 ->
                                   let (elpi__state, elpi__108, elpi__106) =
                                     (fun ~depth ->
                                        fun h ->
                                          fun c ->
                                            fun s ->
                                              fun t ->
                                                elpi_embed_term ~depth h c s
                                                  t) ~depth:elpi__depth
                                       elpi__hyps elpi__constraints
                                       elpi__state elpi__104 in
                                   let (elpi__state, elpi__109, elpi__107) =
                                     (fun ~depth ->
                                        fun h ->
                                          fun c ->
                                            fun s ->
                                              fun t ->
                                                ty.Elpi.API.ContextualConversion.embed
                                                  ~depth h c s t)
                                       ~depth:elpi__depth elpi__hyps
                                       elpi__constraints elpi__state
                                       elpi__105 in
                                   (elpi__state,
                                     (Elpi.API.RawData.mkAppGlobalL
                                        elpi_constant_constructor_term_Castc
                                        [elpi__108; elpi__109]),
                                     (List.concat [elpi__106; elpi__107])))
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state elpi__104 elpi__105
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
                               (Elpi.API.PPX.pp_ctx_entry pp_ctx))
                            elpi__dbl2ctx);
                     (let { Elpi.API.PPX.entry = elpi__entry;
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
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 (let readback = elpi_readback_term in
                                  fun ~depth ->
                                    fun h ->
                                      fun c ->
                                        fun s ->
                                          fun t ->
                                            Elpi.API.Utils.map_acc
                                              (readback ~depth h c) s
                                              (Elpi.API.Utils.lp_list_to_list
                                                 ~depth t)) ~depth h c s t)
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
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__78::elpi__79::[] ->
                         let (elpi__state, elpi__78, elpi__80) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      ty.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__78 in
                         let elpi__ctx_entry =
                           (fun s -> fun ty -> Decl (s, ty)) elpi__83
                             elpi__78 in
                         let elpi__ctx_key =
                           elpi_ctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi.API.PPX.entry = elpi__ctx_entry;
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
                                     (fun ~depth ->
                                        fun h ->
                                          fun c ->
                                            fun s ->
                                              fun t ->
                                                elpi_readback_term ~depth h c
                                                  s t) ~depth:elpi__depth
                                       elpi__hyps elpi__constraints
                                       elpi__state elpi__x in
                                   (match elpi__xs with
                                    | elpi__84::[] ->
                                        let (elpi__state, elpi__84, elpi__85)
                                          =
                                          (fun ~depth ->
                                             fun h ->
                                               fun c ->
                                                 fun s ->
                                                   fun t ->
                                                     ty.Elpi.API.ContextualConversion.readback
                                                       ~depth h c s t)
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
                                            Elpi.API.Ast.Loc.client_payload =
                                              None;
                                            source_name =
                                              "test_two_layers_context.ml";
                                            source_start = 1938;
                                            source_stop = 1938;
                                            line = 65;
                                            line_starts_at = 1927
                                          }
                                     "standard branch readback takes 1 argument or more")
                      ~depth:elpi__depth elpi__hyps elpi__constraints
                      elpi__state (elpi__x :: elpi__xs)
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
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:4 ~variant:0
                 ~ty:kind ~name:"appl" ~doc:"bla bla"
                 ~args:[Elpi.API.ContextualConversion.TyApp
                          ("list",
                            (Elpi.API.ContextualConversion.TyName
                               elpi_constant_type_term), [])];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:4 ~variant:0
                 ~ty:kind ~name:"lam" ~doc:"Lam"
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       ty.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("->",
                           (Elpi.API.ContextualConversion.TyName "term"),
                           [Elpi.API.ContextualConversion.TyName
                              elpi_constant_type_term])];
               Format.fprintf fmt "@[<hov2>type %s@[<hov> %s. %% %s@]@]@\n"
                 "type-cast" "term -> ty -> term" "Cast");
        pp =
          (let rec aux fmt =
             function
             | Var s -> Format.fprintf fmt "%s" s
             | App tl -> Format.fprintf fmt "App %a" (RawPp.list aux " ") tl
             | Lam (s, ty, t) -> Format.fprintf fmt "Lam %s (%a)" s aux t
             | Literal i -> Format.fprintf fmt "%d" i
             | Cast (t, _) -> aux fmt t in
           aux);
        embed = elpi_embed_term;
        readback = elpi_readback_term
      }
    let elpi_term = Elpi.API.BuiltIn.MLDataC term
    let elpi__term__deep_copy =
      "func term.copy term -> term.\nterm.copy (appl A0) (appl B0) :- ((list.copy term.copy) A0 B0).\nterm.copy (lam A0 A1 A2) (lam B0 B1 B2) :- (string.copy A0 B0), (ty.copy A1 B1), (pi x\\ decl x B0 B1 ==> term.copy x x ==> (term.copy (A2 x) (B2 x))).\nterm.copy (type-cast A0 A1) (type-cast B0 B1) :- (term.copy A0 B0), (ty.copy A1 B1).\n\n"
    class ctx_for_term (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_term.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx = context_made_of_tctx.Elpi.API.PPX.get s
        inherit ! ((ctx_for_ctx) h s)
        method ctx = context_made_of_ctx.Elpi.API.PPX.get s
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
              let ctx = (new ctx_for_ctx) h s in
              let (s, gls1) =
                Elpi.API.PPX.readback_context ~depth context_made_of_ctx ctx
                  h c s in
              (s, ((new ctx_for_term) h s), c, (List.concat [gls0; gls1]))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_term; Elpi.API.BuiltIn.LPCode elpi__term__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let term :
  'a 'csts . (term, #ctx_for_term as 'a, 'csts) ContextualConversion.t = term
open BuiltInPredicate.Notation
let term_to_string =
  BuiltInPredicate.ContextualPred
    ("term->string", in_ctx_for_term,
      (In (term, "T", (Out (BuiltInData.stringC, "S", (Read "what else"))))),
      (fun (t : term) ->
         fun (_ety : string BuiltInPredicate.oarg) ->
           fun ~depth:_ ->
             fun c ->
               fun (_cst : Data.constraints) ->
                 fun (_state : State.t) ->
                   !:
                     (Format.asprintf "@[<hov>%a@ %a@ |-@ %a@]@\n%!"
                        (RawData.Constants.Map.pp (PPX.pp_ctx_entry pp_tctx))
                        c#tctx
                        (RawData.Constants.Map.pp (PPX.pp_ctx_entry pp_ctx))
                        c#ctx term.pp t)))
let builtin =
  let open BuiltIn in
    BuiltIn.declare ~file_name
      ((PPX.to_list declaration) @ [MLCode (term_to_string, DocAbove)])
let program =
  {|
main :-
  pi x w y q t\
    tdecl t "alpha" tt ==>
    decl y "arg" (forall "ss" tt s\ mono (tarrow (tconst "nat") s)) ==>
    decl x "f" (mono (tarrow (tconst "nat") t)) ==>
    % the bound variables are copied to themselves
    tye.copy t t ==> term.copy x x ==> term.copy y y ==> (
      sigma T C\
        T = (appl [x, y, lam "zzzz" (mono t) z\ z]),
        print {term->string T},
        term.copy T C,
        print {term->string C}).
|}
let () = Ppx_tests_lib.run_program builtin program
