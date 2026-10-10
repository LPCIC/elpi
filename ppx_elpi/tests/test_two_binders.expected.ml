let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show = Format.asprintf "%a" pp
  end
type tmctx =
  | TmEntry of ((string)[@elpi.key "term"]) [@@elpi.index (module String)]
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_tmctx
      : Ppx_deriving_runtime.Format.formatter ->
          tmctx -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt ->
            function
            | TmEntry a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_two_binders.TmEntry@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])"))
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_tmctx : tmctx -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_tmctx x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_tmctx = "tmctx"
    let elpi_constant_type_tmctxc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_tmctx
    let elpi_constant_constructor_tmctx_TmEntry = "tmentry"
    let elpi_constant_constructor_tmctx_TmEntryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tmctx_TmEntry
    module Elpi_tmctx_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_tmctx_state =
      Elpi.API.State.declare_component ~name:"tmctx"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_tmctx_Map.empty : Elpi.API.RawData.constant
                                            Elpi_tmctx_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : tmctx
                                                             Elpi.API.PPX.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x) ()
    let elpi_tmctx_to_key ~depth:_  elpi__fun_arg =
      match elpi__fun_arg with | TmEntry elpi__11 -> elpi__11
    let elpi_is_tmctx { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x }
      =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_tmctx_TmEntryc)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Utils.type_error
                   "context entry applied to a non bound variable")
          else None
      | _ -> None
    let elpi_push_tmctx ~depth:elpi__depth  elpi__state elpi__name
      elpi__ctx_item =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_tmctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_tmctx_Map.add elpi__name elpi__i elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item
          elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_tmctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    let elpi_pop_tmctx ~depth:elpi__depth  elpi__state elpi__name =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_tmctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_tmctx_Map.remove elpi__name elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_tmctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    module Ctx_for_tmctx =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_tmctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tmctx), 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | (elpi__6, TmEntry elpi__5) ->
                    let (elpi__state, elpi__9, elpi__7) =
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
                        elpi__state elpi__6 in
                    let (elpi__state, elpi__10, elpi__8) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__5 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_tmctx_TmEntryc
                         [elpi__9; elpi__10]),
                      (List.concat [elpi__7; elpi__8]))
    and elpi_readback_tmctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tmctx), 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_tmctx_TmEntryc ->
                    let (elpi__state, elpi__4, elpi__3) =
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
                     | elpi__1::[] ->
                         let (elpi__state, elpi__1, elpi__2) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__1 in
                         (elpi__state, (elpi__4, (TmEntry elpi__1)),
                           (List.concat [elpi__3; elpi__2]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_tmctx_TmEntryc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "tmctx" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and tmctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tmctx), 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "tmctx" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               ();
               Elpi.API.PPX.Doc.context_entry fmt ~name:"tmentry"
                 ~doc:"TmEntry"
                 ~key:(Elpi.API.ContextualConversion.TyName "term")
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_tmctx fmt x);
        embed = elpi_embed_tmctx;
        readback = elpi_readback_tmctx
      }
    let context_made_of_tmctx =
      {
        Elpi.API.PPX.is_entry_for_bound_var = elpi_is_tmctx;
        to_key = elpi_tmctx_to_key;
        push = elpi_push_tmctx;
        pop = elpi_pop_tmctx;
        conv = tmctx;
        init =
          (fun state ->
             Elpi.API.State.set elpi_tmctx_state state
               ((Elpi_tmctx_Map.empty : Elpi.API.RawData.constant
                                          Elpi_tmctx_Map.t),
                 (Elpi.API.RawData.Constants.Map.empty : tmctx
                                                           Elpi.API.PPX.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get =
          (fun state -> snd @@ (Elpi.API.State.get elpi_tmctx_state state))
      }
    let elpi_tmctx = Elpi.API.BuiltIn.MLDataC tmctx
    class ctx_for_tmctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tmctx.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_tmctx :
      (Ctx_for_tmctx.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_tmctx) h s), c, (List.concat []))
    let () = Elpi.API.PPX.add_declarations declaration [elpi_tmctx]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type tyctx =
  | TyEntry of ((string)[@elpi.key "ty"]) [@@elpi.index (module String)]
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_tyctx
      : Ppx_deriving_runtime.Format.formatter ->
          tyctx -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt ->
            function
            | TyEntry a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_two_binders.TyEntry@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])"))
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_tyctx : tyctx -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_tyctx x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_tyctx = "tyctx"
    let elpi_constant_type_tyctxc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_tyctx
    let elpi_constant_constructor_tyctx_TyEntry = "tyentry"
    let elpi_constant_constructor_tyctx_TyEntryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tyctx_TyEntry
    module Elpi_tyctx_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_tyctx_state =
      Elpi.API.State.declare_component ~name:"tyctx"
        ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_tyctx_Map.empty : Elpi.API.RawData.constant
                                            Elpi_tyctx_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : tyctx
                                                             Elpi.API.PPX.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x) ()
    let elpi_tyctx_to_key ~depth:_  elpi__fun_arg =
      match elpi__fun_arg with | TyEntry elpi__22 -> elpi__22
    let elpi_is_tyctx { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x }
      =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_tyctx_TyEntryc)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Utils.type_error
                   "context entry applied to a non bound variable")
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
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_tyctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tyctx), 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | (elpi__17, TyEntry elpi__16) ->
                    let (elpi__state, elpi__20, elpi__18) =
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
                        elpi__state elpi__17 in
                    let (elpi__state, elpi__21, elpi__19) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__16 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_tyctx_TyEntryc
                         [elpi__20; elpi__21]),
                      (List.concat [elpi__18; elpi__19]))
    and elpi_readback_tyctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tyctx), 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_tyctx_TyEntryc ->
                    let (elpi__state, elpi__15, elpi__14) =
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
                     | elpi__12::[] ->
                         let (elpi__state, elpi__12, elpi__13) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__12 in
                         (elpi__state, (elpi__15, (TyEntry elpi__12)),
                           (List.concat [elpi__14; elpi__13]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_tyctx_TyEntryc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "tyctx" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and tyctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tyctx), 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "tyctx" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               ();
               Elpi.API.PPX.Doc.context_entry fmt ~name:"tyentry"
                 ~doc:"TyEntry"
                 ~key:(Elpi.API.ContextualConversion.TyName "ty")
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt -> fun (_, x) -> pp_tyctx fmt x);
        embed = elpi_embed_tyctx;
        readback = elpi_readback_tyctx
      }
    let context_made_of_tyctx =
      {
        Elpi.API.PPX.is_entry_for_bound_var = elpi_is_tyctx;
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
                                                           Elpi.API.PPX.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get =
          (fun state -> snd @@ (Elpi.API.State.get elpi_tyctx_state state))
      }
    let elpi_tyctx = Elpi.API.BuiltIn.MLDataC tyctx
    class ctx_for_tyctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tyctx.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_tyctx :
      (Ctx_for_tyctx.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_tyctx) h s), c, (List.concat []))
    let () = Elpi.API.PPX.add_declarations declaration [elpi_tyctx]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type term =
  | Var of string [@elpi.var tmctx]
  | App of term * term 
  | Lam of string * ((term)[@elpi.binder "term" tmctx (fun s -> TmEntry s)])
  
  | TLam of string * ((term)[@elpi.binder "ty" tyctx (fun s -> TyEntry s)]) 
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_term
      : Ppx_deriving_runtime.Format.formatter ->
          term -> Ppx_deriving_runtime.unit
      =
      ((let __3 = pp_term
        and __2 = pp_term
        and __1 = pp_term
        and __0 = pp_term in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              function
              | Var a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_two_binders.Var@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])")
              | App (a0, a1) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_two_binders.App (@,";
                   ((__0 fmt) a0;
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__1 fmt) a1);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
              | Lam (a0, a1) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_two_binders.Lam (@,";
                   ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__2 fmt) a1);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
              | TLam (a0, a1) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_two_binders.TLam (@,";
                   ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__3 fmt) a1);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_term : term -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_term x[@@ocaml.warning
                                                                    "-32"]
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
    let elpi_constant_constructor_term_TLam = "tlam"
    let elpi_constant_constructor_term_TLamc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_TLam
    module Ctx_for_term =
      struct
        class type t =
          object
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_tyctx.t
            method  tyctx : tyctx Elpi.API.PPX.ctx_field
            inherit Ctx_for_tmctx.t
            method  tmctx : tmctx Elpi.API.PPX.ctx_field
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
                | Var elpi__37 ->
                    let (elpi__ctx2dbl, _) =
                      Elpi.API.State.get elpi_tmctx_state elpi__state in
                    let elpi__key = (fun x -> x) elpi__37 in
                    (if not (Elpi_tmctx_Map.mem elpi__key elpi__ctx2dbl)
                     then Elpi.API.Utils.error "Unbound variable";
                     (elpi__state,
                       (Elpi.API.RawData.mkBound
                          (Elpi_tmctx_Map.find elpi__key elpi__ctx2dbl)), []))
                | App (elpi__40, elpi__41) ->
                    let (elpi__state, elpi__44, elpi__42) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_term ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__40 in
                    let (elpi__state, elpi__45, elpi__43) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_term ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__41 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_term_Appc
                         [elpi__44; elpi__45]),
                      (List.concat [elpi__42; elpi__43]))
                | Lam (elpi__46, elpi__47) ->
                    let (elpi__state, elpi__50, elpi__48) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__46 in
                    let elpi__ctx_entry = (fun s -> TmEntry s) elpi__46 in
                    let elpi__ctx_key =
                      elpi_tmctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                    let elpi__ctx_entry =
                      {
                        Elpi.API.PPX.entry = elpi__ctx_entry;
                        depth = elpi__depth
                      } in
                    let elpi__state =
                      elpi_push_tmctx ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key elpi__ctx_entry in
                    let (elpi__state, elpi__52, elpi__49) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_term ~depth h c s t)
                        ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                        elpi__state elpi__47 in
                    let elpi__51 = Elpi.API.RawData.mkLam elpi__52 in
                    let elpi__state =
                      elpi_pop_tmctx ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_term_Lamc
                         [elpi__50; elpi__51]),
                      (List.concat [elpi__48; elpi__49]))
                | TLam (elpi__53, elpi__54) ->
                    let (elpi__state, elpi__57, elpi__55) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__53 in
                    let elpi__ctx_entry = (fun s -> TyEntry s) elpi__53 in
                    let elpi__ctx_key =
                      elpi_tyctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                    let elpi__ctx_entry =
                      {
                        Elpi.API.PPX.entry = elpi__ctx_entry;
                        depth = elpi__depth
                      } in
                    let elpi__state =
                      elpi_push_tyctx ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key elpi__ctx_entry in
                    let (elpi__state, elpi__59, elpi__56) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_term ~depth h c s t)
                        ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                        elpi__state elpi__54 in
                    let elpi__58 = Elpi.API.RawData.mkLam elpi__59 in
                    let elpi__state =
                      elpi_pop_tyctx ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_term_TLamc
                         [elpi__57; elpi__58]),
                      (List.concat [elpi__55; elpi__56]))
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
                      Elpi.API.State.get elpi_tmctx_state elpi__state in
                    (if
                       not
                         (Elpi.API.RawData.Constants.Map.mem elpi__hd
                            elpi__dbl2ctx)
                     then
                       Elpi.API.Utils.error
                         (Format.asprintf "Unbound variable: %s in %a"
                            (Elpi.API.RawData.Constants.show elpi__hd)
                            (Elpi.API.RawData.Constants.Map.pp
                               (Elpi.API.PPX.pp_ctx_entry pp_tmctx))
                            elpi__dbl2ctx);
                     (let { Elpi.API.PPX.entry = elpi__entry;
                            depth = elpi__depth }
                        =
                        Elpi.API.RawData.Constants.Map.find elpi__hd
                          elpi__dbl2ctx in
                      (elpi__state,
                        (Var
                           (elpi_tmctx_to_key ~depth:elpi__depth elpi__entry)),
                        [])))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Appc ->
                    let (elpi__state, elpi__28, elpi__27) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t -> elpi_readback_term ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__25::[] ->
                         let (elpi__state, elpi__25, elpi__26) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      elpi_readback_term ~depth h c s t)
                             ~depth:elpi__depth elpi__hyps elpi__constraints
                             elpi__state elpi__25 in
                         (elpi__state, (App (elpi__28, elpi__25)),
                           (List.concat [elpi__27; elpi__26]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Appc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Lamc ->
                    let (elpi__state, elpi__32, elpi__31) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__29::[] ->
                         let elpi__ctx_entry = (fun s -> TmEntry s) elpi__32 in
                         let elpi__ctx_key =
                           elpi_tmctx_to_key ~depth:elpi__depth
                             elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi.API.PPX.entry = elpi__ctx_entry;
                             depth = elpi__depth
                           } in
                         let elpi__state =
                           elpi_push_tmctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key elpi__ctx_entry in
                         let (elpi__state, elpi__29, elpi__30) =
                           match Elpi.API.RawData.look ~depth:elpi__depth
                                   elpi__29
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
                           elpi_pop_tmctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state, (Lam (elpi__32, elpi__29)),
                           (List.concat [elpi__31; elpi__30]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Lamc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_TLamc ->
                    let (elpi__state, elpi__36, elpi__35) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__33::[] ->
                         let elpi__ctx_entry = (fun s -> TyEntry s) elpi__36 in
                         let elpi__ctx_key =
                           elpi_tyctx_to_key ~depth:elpi__depth
                             elpi__ctx_entry in
                         let elpi__ctx_entry =
                           {
                             Elpi.API.PPX.entry = elpi__ctx_entry;
                             depth = elpi__depth
                           } in
                         let elpi__state =
                           elpi_push_tyctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key elpi__ctx_entry in
                         let (elpi__state, elpi__33, elpi__34) =
                           match Elpi.API.RawData.look ~depth:elpi__depth
                                   elpi__33
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
                           elpi_pop_tyctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state, (TLam (elpi__36, elpi__33)),
                           (List.concat [elpi__35; elpi__34]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_TLamc)))
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
                 ~ty:kind ~name:"app" ~doc:"App"
                 ~args:[Elpi.API.ContextualConversion.TyName
                          elpi_constant_type_term;
                       Elpi.API.ContextualConversion.TyName
                         elpi_constant_type_term];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:4 ~variant:0
                 ~ty:kind ~name:"lam" ~doc:"Lam"
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("->",
                           (Elpi.API.ContextualConversion.TyName "term"),
                           [Elpi.API.ContextualConversion.TyName
                              elpi_constant_type_term])];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:4 ~variant:0
                 ~ty:kind ~name:"tlam" ~doc:"TLam"
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("->", (Elpi.API.ContextualConversion.TyName "ty"),
                           [Elpi.API.ContextualConversion.TyName
                              elpi_constant_type_term])]);
        pp = pp_term;
        embed = elpi_embed_term;
        readback = elpi_readback_term
      }
    let elpi_term = Elpi.API.BuiltIn.MLDataC term
    let elpi__term__deep_copy =
      "func term.copy term -> term.\nterm.copy (app A0 A1) (app B0 B1) :- (term.copy A0 B0), (term.copy A1 B1).\nterm.copy (lam A0 A1) (lam B0 B1) :- (string.copy A0 B0), (pi x\\ tmentry x B0 ==> term.copy x x ==> (term.copy (A1 x) (B1 x))).\nterm.copy (tlam A0 A1) (tlam B0 B1) :- (string.copy A0 B0), (pi x\\ tyentry x B0 ==> ty.copy x x ==> (term.copy (A1 x) (B1 x))).\n\n"
    class ctx_for_term (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_term.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_tyctx) h s)
        method tyctx = context_made_of_tyctx.Elpi.API.PPX.get s
        inherit ! ((ctx_for_tmctx) h s)
        method tmctx = context_made_of_tmctx.Elpi.API.PPX.get s
      end
    let (in_ctx_for_term :
      (Ctx_for_term.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              let ctx = (new ctx_for_tyctx) h s in
              let (s, gls0) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tyctx
                  ctx h c s in
              let ctx = (new ctx_for_tmctx) h s in
              let (s, gls1) =
                Elpi.API.PPX.readback_context ~depth context_made_of_tmctx
                  ctx h c s in
              (s, ((new ctx_for_term) h s), c, (List.concat [gls0; gls1]))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_term; Elpi.API.BuiltIn.LPCode elpi__term__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let term :
  'c 'csts . (term, #ctx_for_term as 'c, 'csts) ContextualConversion.t = term
let in_ctx_for_term : (ctx_for_term, 'csts) ContextualConversion.ctx_readback
  = in_ctx_for_term
open BuiltInPredicate.Notation
let term_to_string =
  BuiltInPredicate.ContextualPred
    ("term->string", in_ctx_for_term,
      (In (term, "T", (Out (BuiltInData.stringC, "S", (Read "what else"))))),
      (fun (x : term) ->
         fun (_s : string BuiltInPredicate.oarg) ->
           fun ~depth:_ ->
             fun c ->
               fun (_cst : Data.constraints) ->
                 fun (_state : State.t) ->
                   !:
                     (Format.asprintf "@[<hov>%a@ ;@ %a@ |-@ %a@]@\n%!"
                        (RawData.Constants.Map.pp (PPX.pp_ctx_entry pp_tmctx))
                        c#tmctx
                        (RawData.Constants.Map.pp (PPX.pp_ctx_entry pp_tyctx))
                        c#tyctx term.pp x)))
let builtin =
  let open BuiltIn in
    BuiltIn.declare ~file_name
      (((LPCode "data ty.\nfunc ty.copy ty -> ty.") ::
         (PPX.to_list declaration)) @ [MLCode (term_to_string, DocAbove)])
let program =
  {|
main :-
  pi x a\
    tmentry x "x" ==>
    tyentry a "a" ==>
    term.copy x x ==> (
      sigma T C\
        T = (tlam "B" b\ lam "y" y\ app x y),
        print {term->string T},
        % the deep copy goes under both kinds of binders
        term.copy T C,
        print {term->string C}).
|}
let () = Ppx_tests_lib.run_program builtin program
