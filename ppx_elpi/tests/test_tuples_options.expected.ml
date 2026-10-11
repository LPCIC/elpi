let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type color =
  | Red 
  | Green [@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_color
      : Ppx_deriving_runtime.Format.formatter ->
          color -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt ->
            function
            | Red ->
                Ppx_deriving_runtime.Format.pp_print_string fmt
                  "Test_tuples_options.Red"
            | Green ->
                Ppx_deriving_runtime.Format.pp_print_string fmt
                  "Test_tuples_options.Green")
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_color : color -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_color x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_color = "color"
    let elpi_constant_type_colorc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_color
    let elpi_constant_constructor_color_Red = "red"
    let elpi_constant_constructor_color_Redc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_color_Red
    let elpi_constant_constructor_color_Green = "green"
    let elpi_constant_constructor_color_Greenc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_color_Green
    module Ctx_for_color =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_color :
      'c 'csts . (color, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | Red ->
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_color_Redc []),
                      (List.concat []))
                | Green ->
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_color_Greenc []),
                      (List.concat []))
    and elpi_readback_color :
      'c 'csts . (color, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.Const elpi__hd when
                    elpi__hd == elpi_constant_constructor_color_Redc ->
                    (elpi__state, Red, [])
                | Elpi.API.RawData.Const elpi__hd when
                    elpi__hd == elpi_constant_constructor_color_Greenc ->
                    (elpi__state, Green, [])
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "color" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and color : 'c 'csts . (color, 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "color" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:0
                 ~ty:kind ~name:"red" ~doc:"Red" ~args:[];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:0
                 ~ty:kind ~name:"green" ~doc:"Green" ~args:[]);
        pp = pp_color;
        embed = elpi_embed_color;
        readback = elpi_readback_color
      }
    let elpi_color = Elpi.API.BuiltIn.MLDataC color
    let elpi__color__deep_copy =
      "func color.copy color -> color.\ncolor.copy red red.\ncolor.copy green green.\n\n"
    class ctx_for_color (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_color.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_color :
      (Ctx_for_color.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_color) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_color; Elpi.API.BuiltIn.LPCode elpi__color__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type t =
  | P of int * (string * bool) 
  | T of int * string * color 
  | Q of int * string * color * bool 
  | O of color option list [@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp
      : Ppx_deriving_runtime.Format.formatter ->
          t -> Ppx_deriving_runtime.unit
      =
      ((let __2 = pp_color
        and __1 = pp_color
        and __0 = pp_color in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              function
              | P (a0, a1) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_tuples_options.P (@,";
                   ((Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    ((fun (a0, a1) ->
                        Ppx_deriving_runtime.Format.fprintf fmt "(@[";
                        ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                         Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                         (Ppx_deriving_runtime.Format.fprintf fmt "%B") a1);
                        Ppx_deriving_runtime.Format.fprintf fmt "@])")) a1);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
              | T (a0, a1, a2) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_tuples_options.T (@,";
                   (((Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                     Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                     (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__0 fmt) a2);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
              | Q (a0, a1, a2, a3) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_tuples_options.Q (@,";
                   ((((Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                      Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                      (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                     Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                     (__1 fmt) a2);
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (Ppx_deriving_runtime.Format.fprintf fmt "%B") a3);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
              | O a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_tuples_options.O@ ";
                   ((fun x ->
                       Ppx_deriving_runtime.Format.fprintf fmt "@[<2>[";
                       ignore
                         (List.fold_left
                            (fun sep ->
                               fun x ->
                                 if sep
                                 then
                                   Ppx_deriving_runtime.Format.fprintf fmt
                                     ";@ ";
                                 ((function
                                   | None ->
                                       Ppx_deriving_runtime.Format.pp_print_string
                                         fmt "None"
                                   | Some x ->
                                       (Ppx_deriving_runtime.Format.pp_print_string
                                          fmt "(Some ";
                                        (__2 fmt) x;
                                        Ppx_deriving_runtime.Format.pp_print_string
                                          fmt ")"))) x;
                                 true) false x);
                       Ppx_deriving_runtime.Format.fprintf fmt "@,]@]")) a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])"))
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show : t -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp x[@@ocaml.warning
                                                               "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_t = "t"
    let elpi_constant_type_tc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_t
    let elpi_constant_constructor_t_P = "p"
    let elpi_constant_constructor_t_Pc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t_P
    let elpi_constant_constructor_t_T = "t"
    let elpi_constant_constructor_t_Tc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t_T
    let elpi_constant_constructor_t_Q = "q"
    let elpi_constant_constructor_t_Qc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t_Q
    let elpi_constant_constructor_t_O = "o"
    let elpi_constant_constructor_t_Oc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t_O
    module Ctx_for_t =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_t :
      'c 'csts . (t, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | P (elpi__21, elpi__22) ->
                    let (elpi__state, elpi__25, elpi__23) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__21 in
                    let (elpi__state, elpi__26, elpi__24) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 (Elpi.Builtin.PPX.embed_pair
                                    Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                    Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed)
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__22 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_t_Pc [elpi__25; elpi__26]),
                      (List.concat [elpi__23; elpi__24]))
                | T (elpi__27, elpi__28, elpi__29) ->
                    let (elpi__state, elpi__33, elpi__30) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__27 in
                    let (elpi__state, elpi__34, elpi__31) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__28 in
                    let (elpi__state, elpi__35, elpi__32) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 color.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__29 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_t_Tc
                         [elpi__33; elpi__34; elpi__35]),
                      (List.concat [elpi__30; elpi__31; elpi__32]))
                | Q (elpi__36, elpi__37, elpi__38, elpi__39) ->
                    let (elpi__state, elpi__44, elpi__40) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__36 in
                    let (elpi__state, elpi__45, elpi__41) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__37 in
                    let (elpi__state, elpi__46, elpi__42) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 color.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__38 in
                    let (elpi__state, elpi__47, elpi__43) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__39 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_t_Qc
                         [elpi__44; elpi__45; elpi__46; elpi__47]),
                      (List.concat [elpi__40; elpi__41; elpi__42; elpi__43]))
                | O elpi__48 ->
                    let (elpi__state, elpi__50, elpi__49) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 (let embed =
                                    Elpi.Builtin.PPX.embed_option
                                      color.Elpi.API.ContextualConversion.embed in
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
                        elpi__state elpi__48 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_t_Oc [elpi__50]),
                      (List.concat [elpi__49]))
    and elpi_readback_t :
      'c 'csts . (t, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_t_Pc ->
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
                                      (Elpi.Builtin.PPX.readback_pair
                                         Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                         Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback)
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__1 in
                         (elpi__state, (P (elpi__4, elpi__1)),
                           (List.concat [elpi__3; elpi__2]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_t_Pc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_t_Tc ->
                    let (elpi__state, elpi__10, elpi__9) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__5::elpi__6::[] ->
                         let (elpi__state, elpi__5, elpi__7) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__5 in
                         let (elpi__state, elpi__6, elpi__8) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      color.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__6 in
                         (elpi__state, (T (elpi__10, elpi__5, elpi__6)),
                           (List.concat [elpi__9; elpi__7; elpi__8]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_t_Tc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_t_Qc ->
                    let (elpi__state, elpi__18, elpi__17) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__11::elpi__12::elpi__13::[] ->
                         let (elpi__state, elpi__11, elpi__14) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__11 in
                         let (elpi__state, elpi__12, elpi__15) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      color.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__12 in
                         let (elpi__state, elpi__13, elpi__16) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__13 in
                         (elpi__state,
                           (Q (elpi__18, elpi__11, elpi__12, elpi__13)),
                           (List.concat
                              [elpi__17; elpi__14; elpi__15; elpi__16]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_t_Qc)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_t_Oc ->
                    let (elpi__state, elpi__20, elpi__19) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 (let readback =
                                    Elpi.Builtin.PPX.readback_option
                                      color.Elpi.API.ContextualConversion.readback in
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
                         (elpi__state, (O elpi__20),
                           (List.concat [elpi__19]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_t_Oc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a" "t"
                         (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and t : 'c 'csts . (t, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "t" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:0
                 ~ty:kind ~name:"p" ~doc:"P"
                 ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("pair",
                           (Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty),
                           [Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty])];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:0
                 ~ty:kind ~name:"t" ~doc:"T"
                 ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                       Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       color.Elpi.API.ContextualConversion.ty];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:0
                 ~ty:kind ~name:"q" ~doc:"Q"
                 ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                       Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       color.Elpi.API.ContextualConversion.ty;
                       Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:0
                 ~ty:kind ~name:"o" ~doc:"O"
                 ~args:[Elpi.API.ContextualConversion.TyApp
                          ("list",
                            (Elpi.API.ContextualConversion.TyApp
                               ("option",
                                 (color.Elpi.API.ContextualConversion.ty),
                                 [])), [])]);
        pp;
        embed = elpi_embed_t;
        readback = elpi_readback_t
      }
    let elpi_t = Elpi.API.BuiltIn.MLDataC t
    let elpi__t__deep_copy =
      "func t.copy t -> t.\nt.copy (p A0 A1) (p B0 B1) :- (int.copy A0 B0), ((pair.copy string.copy bool.copy) A1 B1).\nt.copy (t A0 A1 A2) (t B0 B1 B2) :- (int.copy A0 B0), (string.copy A1 B1), (color.copy A2 B2).\nt.copy (q A0 A1 A2 A3) (q B0 B1 B2 B3) :- (int.copy A0 B0), (string.copy A1 B1), (color.copy A2 B2), (bool.copy A3 B3).\nt.copy (o A0) (o B0) :- ((list.copy (option.copy color.copy)) A0 B0).\n\n"
    class ctx_for_t (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_t.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_t :
      (Ctx_for_t.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_t) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_t; Elpi.API.BuiltIn.LPCode elpi__t__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type tr = (int * string * color)[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_tr
      : Ppx_deriving_runtime.Format.formatter ->
          tr -> Ppx_deriving_runtime.unit
      =
      ((let __0 = pp_color in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              fun (a0, a1, a2) ->
                Ppx_deriving_runtime.Format.fprintf fmt "(@[";
                (((Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                 Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                 (__0 fmt) a2);
                Ppx_deriving_runtime.Format.fprintf fmt "@])")
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_tr : tr -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_tr x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_tr = "tr"
    let elpi_constant_type_trc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_tr
    module Ctx_for_tr =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_tr :
      'c 'csts . (tr, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                (Elpi.Builtin.PPX.embed_triple
                   Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                   color.Elpi.API.ContextualConversion.embed) ~depth h c s t
    and elpi_readback_tr :
      'c 'csts . (tr, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                (Elpi.Builtin.PPX.readback_triple
                   Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                   color.Elpi.API.ContextualConversion.readback) ~depth h c s
                  t
    and tr : 'c 'csts . (tr, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "tr" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt -> fun () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:""; ());
        pp = pp_tr;
        embed = elpi_embed_tr;
        readback = elpi_readback_tr
      }
    let elpi_tr =
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           ("tr" ^
              (" " ^
                 (((let open Elpi.API.PPX.Doc in show_ty_ast ~prec:AppArg) @@
                     (Elpi.Builtin.PPX.triple Elpi.API.BuiltInData.intC
                        Elpi.API.BuiltInData.stringC color).Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "tr")))))
    let elpi__tr__deep_copy =
      "func tr.copy tr -> tr.\ntr.copy A B :- ((triple.copy int.copy string.copy color.copy) A B)."
    class ctx_for_tr (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tr.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_tr :
      (Ctx_for_tr.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_tr) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_tr; Elpi.API.BuiltIn.LPCode elpi__tr__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type qd = (int * string * color * bool)[@@deriving
                                         (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_qd
      : Ppx_deriving_runtime.Format.formatter ->
          qd -> Ppx_deriving_runtime.unit
      =
      ((let __0 = pp_color in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              fun (a0, a1, a2, a3) ->
                Ppx_deriving_runtime.Format.fprintf fmt "(@[";
                ((((Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__0 fmt) a2);
                 Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%B") a3);
                Ppx_deriving_runtime.Format.fprintf fmt "@])")
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_qd : qd -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_qd x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_qd = "qd"
    let elpi_constant_type_qdc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_qd
    module Ctx_for_qd =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_qd :
      'c 'csts . (qd, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                (Elpi.Builtin.PPX.embed_quadruple
                   Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                   color.Elpi.API.ContextualConversion.embed
                   Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed)
                  ~depth h c s t
    and elpi_readback_qd :
      'c 'csts . (qd, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                (Elpi.Builtin.PPX.readback_quadruple
                   Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                   color.Elpi.API.ContextualConversion.readback
                   Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback)
                  ~depth h c s t
    and qd : 'c 'csts . (qd, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "qd" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt -> fun () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:""; ());
        pp = pp_qd;
        embed = elpi_embed_qd;
        readback = elpi_readback_qd
      }
    let elpi_qd =
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           ("qd" ^
              (" " ^
                 (((let open Elpi.API.PPX.Doc in show_ty_ast ~prec:AppArg) @@
                     (Elpi.Builtin.PPX.quadruple Elpi.API.BuiltInData.intC
                        Elpi.API.BuiltInData.stringC color
                        Elpi.Builtin.PPX.bool).Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "qd")))))
    let elpi__qd__deep_copy =
      "func qd.copy qd -> qd.\nqd.copy A B :- ((quadruple.copy int.copy string.copy color.copy bool.copy) A B)."
    class ctx_for_qd (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_qd.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_qd :
      (Ctx_for_qd.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_qd) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_qd; Elpi.API.BuiltIn.LPCode elpi__qd__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let t : 'c 'csts . (t, 'c, 'csts) ContextualConversion.t = t
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let program =
  {|
main :-
  t.copy (p 1 (pr "s" tt)) (p 1 (pr "s" tt)),
  t.copy (t 1 "s" red) (t 1 "s" red),
  t.copy (q 1 "s" green ff) (q 1 "s" green ff),
  t.copy (o [some red, none]) X, X = o [some red, none],
  tr.copy (triple 1 "s" red) (triple 1 "s" red),
  qd.copy (quadruple 1 "s" red tt) (quadruple 1 "s" red tt).
|}
let () = Ppx_tests_lib.run_program builtin program
