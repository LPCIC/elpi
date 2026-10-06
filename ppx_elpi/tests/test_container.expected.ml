let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type 'a located = {
  loc: int ;
  data: 'a }[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_located
      : 'a .
          (Ppx_deriving_runtime.Format.formatter ->
             'a -> Ppx_deriving_runtime.unit)
            ->
            Ppx_deriving_runtime.Format.formatter ->
              'a located -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun poly_a ->
            fun fmt ->
              fun x ->
                Ppx_deriving_runtime.Format.fprintf fmt "@[<2>{ ";
                ((Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ "
                    "Test_container.loc";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%d") x.loc;
                  Ppx_deriving_runtime.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
                 Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "data";
                 (poly_a fmt) x.data;
                 Ppx_deriving_runtime.Format.fprintf fmt "@]");
                Ppx_deriving_runtime.Format.fprintf fmt "@ }@]")
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_located :
      'a .
        (Ppx_deriving_runtime.Format.formatter ->
           'a -> Ppx_deriving_runtime.unit)
          -> 'a located -> Ppx_deriving_runtime.string
      =
      fun poly_a ->
        fun x ->
          Ppx_deriving_runtime.Format.asprintf "%a" (pp_located poly_a) x
    [@@ocaml.warning "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_located = "located"
    let elpi_constant_type_locatedc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_located
    let elpi_constant_constructor_located_located = "located"
    let elpi_constant_constructor_located_locatedc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_located_located
    module Ctx_for_located =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_located :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.embedding
          ->
          ('elpi__param__a located, 'c, 'csts)
            Elpi.API.ContextualConversion.embedding
      =
      fun elpi_embed_elpi__param__a ->
        fun ~depth:elpi__depth ->
          fun elpi__hyps ->
            fun elpi__constraints ->
              fun elpi__state ->
                fun elpi__fun_arg ->
                  match elpi__fun_arg with
                  | { loc = elpi__5; data = elpi__6 } ->
                      let (elpi__state, elpi__9, elpi__7) =
                        (fun ~depth ->
                           fun h ->
                             fun c ->
                               fun s ->
                                 fun t ->
                                   Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                     ~depth h c s t) ~depth:elpi__depth
                          elpi__hyps elpi__constraints elpi__state elpi__5 in
                      let (elpi__state, elpi__10, elpi__8) =
                        (fun ~depth ->
                           fun h ->
                             fun c ->
                               fun s ->
                                 fun t ->
                                   elpi_embed_elpi__param__a ~depth h c s t)
                          ~depth:elpi__depth elpi__hyps elpi__constraints
                          elpi__state elpi__6 in
                      (elpi__state,
                        (Elpi.API.RawData.mkAppGlobalL
                           elpi_constant_constructor_located_locatedc
                           [elpi__9; elpi__10]),
                        (List.concat [elpi__7; elpi__8]))
    and elpi_readback_located :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.readback
          ->
          ('elpi__param__a located, 'c, 'csts)
            Elpi.API.ContextualConversion.readback
      =
      fun elpi_readback_elpi__param__a ->
        fun ~depth:elpi__depth ->
          fun elpi__hyps ->
            fun elpi__constraints ->
              fun elpi__state ->
                fun elpi__x ->
                  match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                  | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                      elpi__hd == elpi_constant_constructor_located_locatedc
                      ->
                      let (elpi__state, elpi__4, elpi__3) =
                        (fun ~depth ->
                           fun h ->
                             fun c ->
                               fun s ->
                                 fun t ->
                                   Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                                     ~depth h c s t) ~depth:elpi__depth
                          elpi__hyps elpi__constraints elpi__state elpi__x in
                      (match elpi__xs with
                       | elpi__1::[] ->
                           let (elpi__state, elpi__1, elpi__2) =
                             (fun ~depth ->
                                fun h ->
                                  fun c ->
                                    fun s ->
                                      fun t ->
                                        elpi_readback_elpi__param__a ~depth h
                                          c s t) ~depth:elpi__depth
                               elpi__hyps elpi__constraints elpi__state
                               elpi__1 in
                           (elpi__state, { loc = elpi__4; data = elpi__1 },
                             (List.concat [elpi__3; elpi__2]))
                       | _ ->
                           Elpi.API.Utils.type_error
                             ("Not enough arguments to constructor: " ^
                                (Elpi.API.RawData.Constants.show
                                   elpi_constant_constructor_located_locatedc)))
                  | _ ->
                      Elpi.API.Utils.type_error
                        (Format.asprintf "Not a constructor of type %s: %a"
                           "located" (Elpi.API.RawPp.term elpi__depth)
                           elpi__x)
    and located :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.t ->
          ('elpi__param__a located, 'c, 'csts)
            Elpi.API.ContextualConversion.t
      =
      fun elpi__param__a ->
        let kind =
          Elpi.API.ContextualConversion.TyApp
            ("located", (elpi__param__a.Elpi.API.ContextualConversion.ty),
              []) in
        {
          Elpi.API.ContextualConversion.ty = kind;
          pp_doc =
            (fun fmt ->
               fun () ->
                 Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
                 Elpi.API.PPX.Doc.constructor fmt ~max_name_len:7 ~variant:0
                   ~ty:kind ~name:"located" ~doc:"located"
                   ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                         elpi__param__a.Elpi.API.ContextualConversion.ty]);
          pp = (pp_located elpi__param__a.pp);
          embed =
            (elpi_embed_located
               elpi__param__a.Elpi.API.ContextualConversion.embed);
          readback =
            (elpi_readback_located
               elpi__param__a.Elpi.API.ContextualConversion.readback)
        }
    let elpi_located =
      Elpi.API.BuiltIn.MLDataC (located (Elpi.API.BuiltInData.polyC "A"))
    let elpi__located__deep_copy =
      "func located.copy (func X0 -> Y0), located X0 -> located Y0.\nlocated.copy F0 (located A0 A1) (located B0 B1) :- (int.copy A0 B0), (F0 A1 B1).\n\n"
    class ctx_for_located (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_located.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_located :
      (Ctx_for_located.t, 'csts) Elpi.API.ContextualConversion.ctx_readback)
      =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_located) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_located; Elpi.API.BuiltIn.LPCode elpi__located__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type term =
  | A of int 
  | B of string * bool [@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_term
      : Ppx_deriving_runtime.Format.formatter ->
          term -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt ->
            function
            | A a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_container.A@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | B (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_container.B (@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%B") a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_term : term -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_term x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_term = "term"
    let elpi_constant_type_termc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_term
    let elpi_constant_constructor_term_A = "a"
    let elpi_constant_constructor_term_Ac =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_A
    let elpi_constant_constructor_term_B = "b"
    let elpi_constant_constructor_term_Bc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_B
    module Ctx_for_term =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_term :
      'c 'csts . (term, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | A elpi__17 ->
                    let (elpi__state, elpi__19, elpi__18) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__17 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_term_Ac [elpi__19]),
                      (List.concat [elpi__18]))
                | B (elpi__20, elpi__21) ->
                    let (elpi__state, elpi__24, elpi__22) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__20 in
                    let (elpi__state, elpi__25, elpi__23) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__21 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_term_Bc
                         [elpi__24; elpi__25]),
                      (List.concat [elpi__22; elpi__23]))
    and elpi_readback_term :
      'c 'csts . (term, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Ac ->
                    let (elpi__state, elpi__12, elpi__11) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | [] ->
                         (elpi__state, (A elpi__12),
                           (List.concat [elpi__11]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Ac)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Bc ->
                    let (elpi__state, elpi__16, elpi__15) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__13::[] ->
                         let (elpi__state, elpi__13, elpi__14) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__13 in
                         (elpi__state, (B (elpi__16, elpi__13)),
                           (List.concat [elpi__15; elpi__14]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Bc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "term" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and term : 'c 'csts . (term, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "term" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:0
                 ~ty:kind ~name:"a" ~doc:"A"
                 ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:0
                 ~ty:kind ~name:"b" ~doc:"B"
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty]);
        pp = pp_term;
        embed = elpi_embed_term;
        readback = elpi_readback_term
      }
    let elpi_term = Elpi.API.BuiltIn.MLDataC term
    let elpi__term__deep_copy =
      "func term.copy term -> term.\nterm.copy (a A0) (a B0) :- (int.copy A0 B0).\nterm.copy (b A0 A1) (b B0 B1) :- (string.copy A0 B0), (bool.copy A1 B1).\n\n"
    class ctx_for_term (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_term.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_term :
      (Ctx_for_term.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_term) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_term; Elpi.API.BuiltIn.LPCode elpi__term__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type x = (term located * int)[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_x
      : Ppx_deriving_runtime.Format.formatter ->
          x -> Ppx_deriving_runtime.unit
      =
      ((let __1 = pp_located
        and __0 = pp_term in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              fun (a0, a1) ->
                Ppx_deriving_runtime.Format.fprintf fmt "(@[";
                ((__1 (fun fmt -> __0 fmt) fmt) a0;
                 Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a1);
                Ppx_deriving_runtime.Format.fprintf fmt "@])")
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_x : x -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_x x[@@ocaml.warning
                                                                 "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_x = "x"
    let elpi_constant_type_xc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_x
    module Ctx_for_x =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_x :
      'c 'csts . (x, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                (Elpi.Builtin.PPX.embed_pair
                   (located term).Elpi.API.ContextualConversion.embed
                   Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed)
                  ~depth h c s t
    and elpi_readback_x :
      'c 'csts . (x, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                (Elpi.Builtin.PPX.readback_pair
                   (located term).Elpi.API.ContextualConversion.readback
                   Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback)
                  ~depth h c s t
    and x : 'c 'csts . (x, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "x" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt -> fun () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:""; ());
        pp = pp_x;
        embed = elpi_embed_x;
        readback = elpi_readback_x
      }
    let elpi_x =
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           ("x" ^
              (" " ^
                 (((let open Elpi.API.PPX.Doc in show_ty_ast ~prec:AppArg) @@
                     (Elpi.Builtin.PPX.pair (located term)
                        Elpi.API.BuiltInData.intC).Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "x")))))
    let elpi__x__deep_copy =
      "func x.copy x -> x.\nx.copy A B :- ((pair.copy (located.copy term.copy) int.copy) A B)."
    class ctx_for_x (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_x.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_x :
      (Ctx_for_x.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_x) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_x; Elpi.API.BuiltIn.LPCode elpi__x__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let x : 'c 'csts . (x, 'c, 'csts) ContextualConversion.t = x
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let () = Ppx_tests_lib.check_declarations builtin
