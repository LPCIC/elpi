let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show = Format.asprintf "%a" pp
  end
type tctx =
  | Entry of bool * ((string)[@elpi.key "term"]) [@@elpi.index
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
            | Entry (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_simple_contextual_key_last.Entry (@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "%B") a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
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
    let elpi_constant_constructor_tctx_Entry = "entry"
    let elpi_constant_constructor_tctx_Entryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tctx_Entry
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
      match elpi__fun_arg with | Entry (_, elpi__16) -> elpi__16
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
                | (elpi__9, Entry (elpi__7, elpi__8)) ->
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
                                 Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__7 in
                    let (elpi__state, elpi__15, elpi__12) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__8 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_tctx_Entryc
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
                    elpi__hd == elpi_constant_constructor_tctx_Entryc ->
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
                                      Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__1 in
                         let (elpi__state, elpi__2, elpi__4) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__2 in
                         (elpi__state, (elpi__6, (Entry (elpi__1, elpi__2))),
                           (List.concat [elpi__5; elpi__3; elpi__4]))
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
               Elpi.API.PPX.Doc.context_entry fmt ~name:"entry" ~doc:"Entry"
                 ~key:(Elpi.API.ContextualConversion.TyName "term")
                 ~args:[Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty;
                       Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty]);
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
let tctx : 'c 'csts . ((int * tctx), 'c, 'csts) ContextualConversion.t = tctx
let context_made_of_tctx :
  'c 'csts . (tctx, string, #ctx_for_tctx as 'c, 'csts) PPX.context =
  context_made_of_tctx
let in_ctx_for_tctx : (ctx_for_tctx, 'csts) ContextualConversion.ctx_readback
  = in_ctx_for_tctx
type term =
  | Var of string [@elpi.var tctx]
  | App of term * term 
  | Lam of bool * string *
  ((term)[@elpi.binder "term" tctx (fun b -> fun s -> Entry (b, s))]) 
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_term
      : Ppx_deriving_runtime.Format.formatter ->
          term -> Ppx_deriving_runtime.unit
      =
      ((let __2 = pp_term
        and __1 = pp_term
        and __0 = pp_term in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              function
              | Var a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_simple_contextual_key_last.Var@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])")
              | App (a0, a1) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_simple_contextual_key_last.App (@,";
                   ((__0 fmt) a0;
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__1 fmt) a1);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
              | Lam (a0, a1, a2) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_simple_contextual_key_last.Lam (@,";
                   (((Ppx_deriving_runtime.Format.fprintf fmt "%B") a0;
                     Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                     (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__2 fmt) a2);
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
    module Ctx_for_term =
      struct
        class type t =
          object
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi.API.PPX.ctx_field
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
                | Var elpi__29 ->
                    let (elpi__ctx2dbl, _) =
                      Elpi.API.State.get elpi_tctx_state elpi__state in
                    let elpi__key = (fun x -> x) elpi__29 in
                    (if not (Elpi_tctx_Map.mem elpi__key elpi__ctx2dbl)
                     then Elpi.API.Utils.error "Unbound variable";
                     (elpi__state,
                       (Elpi.API.RawData.mkBound
                          (Elpi_tctx_Map.find elpi__key elpi__ctx2dbl)), []))
                | App (elpi__32, elpi__33) ->
                    let (elpi__state, elpi__36, elpi__34) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_term ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__32 in
                    let (elpi__state, elpi__37, elpi__35) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_term ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__33 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_term_Appc
                         [elpi__36; elpi__37]),
                      (List.concat [elpi__34; elpi__35]))
                | Lam (elpi__38, elpi__39, elpi__40) ->
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
                      (fun b -> fun s -> Entry (b, s)) elpi__38 elpi__39 in
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
                    let (elpi__state, elpi__47, elpi__43) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s -> fun t -> elpi_embed_term ~depth h c s t)
                        ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                        elpi__state elpi__40 in
                    let elpi__46 = Elpi.API.RawData.mkLam elpi__47 in
                    let elpi__state =
                      elpi_pop_tctx ~depth:(elpi__depth + 1) elpi__state
                        elpi__ctx_key in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_term_Lamc
                         [elpi__44; elpi__45; elpi__46]),
                      (List.concat [elpi__41; elpi__42; elpi__43]))
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
                               (Elpi.API.PPX.pp_ctx_entry pp_tctx))
                            elpi__dbl2ctx);
                     (let { Elpi.API.PPX.entry = elpi__entry;
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
                    let (elpi__state, elpi__22, elpi__21) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t -> elpi_readback_term ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__19::[] ->
                         let (elpi__state, elpi__19, elpi__20) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      elpi_readback_term ~depth h c s t)
                             ~depth:elpi__depth elpi__hyps elpi__constraints
                             elpi__state elpi__19 in
                         (elpi__state, (App (elpi__22, elpi__19)),
                           (List.concat [elpi__21; elpi__20]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Appc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Lamc ->
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
                           (fun b -> fun s -> Entry (b, s)) elpi__28 elpi__23 in
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
                                           elpi_readback_term ~depth h c s t))
                                 ~depth:(elpi__depth + 1) elpi__hyps
                                 elpi__constraints elpi__state elpi__bo
                           | _ -> assert false in
                         let elpi__state =
                           elpi_pop_tctx ~depth:elpi__depth elpi__state
                             elpi__ctx_key in
                         (elpi__state, (Lam (elpi__28, elpi__23, elpi__24)),
                           (List.concat [elpi__27; elpi__25; elpi__26]))
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
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:3 ~variant:0
                 ~ty:kind ~name:"app" ~doc:"App"
                 ~args:[Elpi.API.ContextualConversion.TyName
                          elpi_constant_type_term;
                       Elpi.API.ContextualConversion.TyName
                         elpi_constant_type_term];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:3 ~variant:0
                 ~ty:kind ~name:"lam" ~doc:"Lam"
                 ~args:[Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty;
                       Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
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
    let elpi__term__deep_copy =
      "func term.copy term -> term.\nterm.copy (app A0 A1) (app B0 B1) :- (term.copy A0 B0), (term.copy A1 B1).\nterm.copy (lam A0 A1 A2) (lam B0 B1 B2) :- (bool.copy A0 B0), (string.copy A1 B1), (pi x\\ entry x B0 B1 ==> term.copy x x ==> (term.copy (A2 x) (B2 x))).\n\n"
    class ctx_for_term (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_term.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx = context_made_of_tctx.Elpi.API.PPX.get s
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
      (fun (t : term) ->
         fun (_ety : string BuiltInPredicate.oarg) ->
           fun ~depth:_ ->
             fun c ->
               fun (_cst : Data.constraints) ->
                 fun (_state : State.t) ->
                   !:
                     (Format.asprintf "@[<hov>%a@ |-@ %a@]@\n%!"
                        (RawData.Constants.Map.pp (PPX.pp_ctx_entry pp_tctx))
                        c#tctx term.pp t)))
let builtin =
  let open BuiltIn in
    BuiltIn.declare ~file_name
      ((PPX.to_list declaration) @ [MLCode (term_to_string, DocAbove)])
let () = Ppx_tests_lib.check_declarations builtin
