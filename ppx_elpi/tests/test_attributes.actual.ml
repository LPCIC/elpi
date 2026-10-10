let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type color =
  | Red 
  | Green 
  | Blue of int [@@elpi.type_doc "The colours"][@@elpi.default_constructor_readback
                                                 fun _default ->
                                                   fun ~depth ->
                                                     fun _ ->
                                                       fun _ ->
                                                         fun state ->
                                                           fun _ ->
                                                             (state, Red, [])]
[@@deriving (show, (elpi { declaration }))]
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
                  "Test_attributes.Red"
            | Green ->
                Ppx_deriving_runtime.Format.pp_print_string fmt
                  "Test_attributes.Green"
            | Blue a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_attributes.Blue@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])"))
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
    let elpi_constant_constructor_color_Blue = "blue"
    let elpi_constant_constructor_color_Bluec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_color_Blue
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
                | Blue elpi__3 ->
                    let (elpi__state, elpi__5, elpi__4) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__3 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_color_Bluec [elpi__5]),
                      (List.concat [elpi__4]))
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
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_color_Bluec ->
                    let (elpi__state, elpi__2, elpi__1) =
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
                         (elpi__state, (Blue elpi__2),
                           (List.concat [elpi__1]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_color_Bluec)))
                | _ ->
                    ((fun _default ->
                        fun ~depth ->
                          fun _ ->
                            fun _ -> fun state -> fun _ -> (state, Red, [])))
                      (fun ~depth:elpi__depth ->
                         fun elpi__hyps ->
                           fun elpi__constraints ->
                             fun elpi__state ->
                               fun elpi__x ->
                                 Elpi.API.Utils.type_error
                                   (Format.asprintf
                                      "Not a constructor of type %s: %a"
                                      "color"
                                      (Elpi.API.RawPp.term elpi__depth)
                                      elpi__x)) ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__x
    and color : 'c 'csts . (color, 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "color" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"The colours";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:0
                 ~ty:kind ~name:"red" ~doc:"Red" ~args:[];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:0
                 ~ty:kind ~name:"green" ~doc:"Green" ~args:[];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:0
                 ~ty:kind ~name:"blue" ~doc:"Blue"
                 ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty]);
        pp = pp_color;
        embed = elpi_embed_color;
        readback = elpi_readback_color
      }
    let elpi_color = Elpi.API.BuiltIn.MLDataC color
    let elpi__color__deep_copy =
      "func color.copy color -> color.\ncolor.copy red red.\ncolor.copy green green.\ncolor.copy (blue A0) (blue B0) :- (int.copy A0 B0).\n\n"
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
type shape =
  | Circle of int [@elpi.code "round"][@elpi.doc "A circle"]
  | Square of int 
  | Hidden of color [@elpi.skip ][@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_shape
      : Ppx_deriving_runtime.Format.formatter ->
          shape -> Ppx_deriving_runtime.unit
      =
      ((let __0 = pp_color in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              function
              | Circle a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_attributes.Circle@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])")
              | Square a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_attributes.Square@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])")
              | Hidden a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_attributes.Hidden@ ";
                   (__0 fmt) a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])"))
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_shape : shape -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_shape x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_shape = "shape"
    let elpi_constant_type_shapec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_shape
    let elpi_constant_constructor_shape_Circle = "round"
    let elpi_constant_constructor_shape_Circlec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_shape_Circle
    let elpi_constant_constructor_shape_Square = "square"
    let elpi_constant_constructor_shape_Squarec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_shape_Square
    module Ctx_for_shape =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_shape :
      'c 'csts . (shape, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | Circle elpi__10 ->
                    let (elpi__state, elpi__12, elpi__11) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__10 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_shape_Circlec [elpi__12]),
                      (List.concat [elpi__11]))
                | Square elpi__13 ->
                    let (elpi__state, elpi__15, elpi__14) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__13 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_shape_Squarec [elpi__15]),
                      (List.concat [elpi__14]))
                | Hidden _ ->
                    Elpi.API.Utils.error
                      ("constructor " ^ ("Hidden" ^ " is not supported"))
    and elpi_readback_shape :
      'c 'csts . (shape, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_shape_Circlec ->
                    let (elpi__state, elpi__7, elpi__6) =
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
                         (elpi__state, (Circle elpi__7),
                           (List.concat [elpi__6]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_shape_Circlec)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_shape_Squarec ->
                    let (elpi__state, elpi__9, elpi__8) =
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
                         (elpi__state, (Square elpi__9),
                           (List.concat [elpi__8]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_shape_Squarec)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "shape" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and shape : 'c 'csts . (shape, 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "shape" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:6 ~variant:0
                 ~ty:kind ~name:"round" ~doc:"A circle"
                 ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:6 ~variant:0
                 ~ty:kind ~name:"square" ~doc:"Square"
                 ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty]);
        pp = pp_shape;
        embed = elpi_embed_shape;
        readback = elpi_readback_shape
      }
    let elpi_shape = Elpi.API.BuiltIn.MLDataC shape
    let elpi__shape__deep_copy =
      "func shape.copy shape -> shape.\nshape.copy (round A0) (round B0) :- (int.copy A0 B0).\nshape.copy (square A0) (square B0) :- (int.copy A0 B0).\n\n"
    class ctx_for_shape (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_shape.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_shape :
      (Ctx_for_shape.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_shape) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_shape; Elpi.API.BuiltIn.LPCode elpi__shape__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type nested =
  | N of shape list option * (int * color list) [@@elpi.type_code "nest"]
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_nested
      : Ppx_deriving_runtime.Format.formatter ->
          nested -> Ppx_deriving_runtime.unit
      =
      ((let __1 = pp_color
        and __0 = pp_shape in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              function
              | N (a0, a1) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_attributes.N (@,";
                   (((function
                      | None ->
                          Ppx_deriving_runtime.Format.pp_print_string fmt
                            "None"
                      | Some x ->
                          (Ppx_deriving_runtime.Format.pp_print_string fmt
                             "(Some ";
                           ((fun x ->
                               Ppx_deriving_runtime.Format.fprintf fmt
                                 "@[<2>[";
                               ignore
                                 (List.fold_left
                                    (fun sep ->
                                       fun x ->
                                         if sep
                                         then
                                           Ppx_deriving_runtime.Format.fprintf
                                             fmt ";@ ";
                                         (__0 fmt) x;
                                         true) false x);
                               Ppx_deriving_runtime.Format.fprintf fmt
                                 "@,]@]")) x;
                           Ppx_deriving_runtime.Format.pp_print_string fmt
                             ")"))) a0;
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    ((fun (a0, a1) ->
                        Ppx_deriving_runtime.Format.fprintf fmt "(@[";
                        ((Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                         Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                         ((fun x ->
                             Ppx_deriving_runtime.Format.fprintf fmt "@[<2>[";
                             ignore
                               (List.fold_left
                                  (fun sep ->
                                     fun x ->
                                       if sep
                                       then
                                         Ppx_deriving_runtime.Format.fprintf
                                           fmt ";@ ";
                                       (__1 fmt) x;
                                       true) false x);
                             Ppx_deriving_runtime.Format.fprintf fmt "@,]@]"))
                           a1);
                        Ppx_deriving_runtime.Format.fprintf fmt "@])")) a1);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_nested : nested -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_nested x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_nested = "nest"
    let elpi_constant_type_nestedc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_nested
    let elpi_constant_constructor_nested_N = "n"
    let elpi_constant_constructor_nested_Nc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_nested_N
    module Ctx_for_nested =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_nested :
      'c 'csts . (nested, 'c, 'csts) Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | N (elpi__20, elpi__21) ->
                    let (elpi__state, elpi__24, elpi__22) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 (Elpi.Builtin.PPX.embed_option
                                    (let embed =
                                       shape.Elpi.API.ContextualConversion.embed in
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
                                                    l), eg))) ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__20 in
                    let (elpi__state, elpi__25, elpi__23) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 (Elpi.Builtin.PPX.embed_pair
                                    Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                    (let embed =
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
                                                    l), eg))) ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__21 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_nested_Nc
                         [elpi__24; elpi__25]),
                      (List.concat [elpi__22; elpi__23]))
    and elpi_readback_nested :
      'c 'csts . (nested, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_nested_Nc ->
                    let (elpi__state, elpi__19, elpi__18) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 (Elpi.Builtin.PPX.readback_option
                                    (let readback =
                                       shape.Elpi.API.ContextualConversion.readback in
                                     fun ~depth ->
                                       fun h ->
                                         fun c ->
                                           fun s ->
                                             fun t ->
                                               Elpi.API.Utils.map_acc
                                                 (readback ~depth h c) s
                                                 (Elpi.API.Utils.lp_list_to_list
                                                    ~depth t))) ~depth h c s
                                   t) ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__16::[] ->
                         let (elpi__state, elpi__16, elpi__17) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      (Elpi.Builtin.PPX.readback_pair
                                         Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                                         (let readback =
                                            color.Elpi.API.ContextualConversion.readback in
                                          fun ~depth ->
                                            fun h ->
                                              fun c ->
                                                fun s ->
                                                  fun t ->
                                                    Elpi.API.Utils.map_acc
                                                      (readback ~depth h c) s
                                                      (Elpi.API.Utils.lp_list_to_list
                                                         ~depth t))) ~depth h
                                        c s t) ~depth:elpi__depth elpi__hyps
                             elpi__constraints elpi__state elpi__16 in
                         (elpi__state, (N (elpi__19, elpi__16)),
                           (List.concat [elpi__18; elpi__17]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_nested_Nc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "nested" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and nested :
      'c 'csts . (nested, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "nest" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:0
                 ~ty:kind ~name:"n" ~doc:"N"
                 ~args:[Elpi.API.ContextualConversion.TyApp
                          ("option",
                            (Elpi.API.ContextualConversion.TyApp
                               ("list",
                                 (shape.Elpi.API.ContextualConversion.ty),
                                 [])), []);
                       Elpi.API.ContextualConversion.TyApp
                         ("pair",
                           (Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty),
                           [Elpi.API.ContextualConversion.TyApp
                              ("list",
                                (color.Elpi.API.ContextualConversion.ty), [])])]);
        pp = pp_nested;
        embed = elpi_embed_nested;
        readback = elpi_readback_nested
      }
    let elpi_nested = Elpi.API.BuiltIn.MLDataC nested
    let elpi__nested__deep_copy =
      "func nest.copy nest -> nest.\nnest.copy (n A0 A1) (n B0 B1) :- ((option.copy (list.copy shape.copy)) A0 B0), ((pair.copy int.copy (list.copy color.copy)) A1 B1).\n\n"
    class ctx_for_nested (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_nested.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_nested :
      (Ctx_for_nested.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_nested) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_nested; Elpi.API.BuiltIn.LPCode elpi__nested__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let colors : (color list, PPX.ctx, Data.constraints) ContextualConversion.t =
  Elpi.API.BuiltInData.listC color
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let () = Ppx_tests_lib.check_declarations builtin
