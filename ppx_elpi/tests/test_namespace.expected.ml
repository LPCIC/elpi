let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type value =
  | Null 
  | Number of int 
  | Pair of value * value [@elpi.code "pair-of-values"][@@elpi.namespace
                                                         "val"][@@deriving
                                                                 (show,
                                                                   (elpi
                                                                    {
                                                                    declaration
                                                                    }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_value :
      Ppx_deriving_runtime.Format.formatter ->
        value -> Ppx_deriving_runtime.unit
      =
      let __1 = pp_value
      and __0 = pp_value in
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | Null ->
                Ppx_deriving_runtime.Format.pp_print_string fmt
                  "Test_namespace.Null"
            | Number a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_namespace.Number@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | Pair (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_namespace.Pair (@,";
                 ((__0 fmt) a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__1 fmt) a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
        [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_value : value -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_value x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_value = "value"
    let elpi_constant_type_valuec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_value
    let elpi_constant_constructor_value_Null = "val.null"
    let elpi_constant_constructor_value_Nullc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_value_Null
    let elpi_constant_constructor_value_Number = "val.number"
    let elpi_constant_constructor_value_Numberc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_value_Number
    let elpi_constant_constructor_value_Pair = "pair-of-values"
    let elpi_constant_constructor_value_Pairc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_value_Pair
    module Ctx_for_value =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_value :
      'c 'csts . (value, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | Null ->
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_value_Nullc []), (List.concat []))
        | Number elpi__7 ->
            let (elpi__state, elpi__9, elpi__8) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__7 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_value_Numberc [elpi__9]),
              (List.concat [elpi__8]))
        | Pair (elpi__10, elpi__11) ->
            let (elpi__state, elpi__14, elpi__12) =
              (fun ~depth h c s t -> elpi_embed_value ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__10 in
            let (elpi__state, elpi__15, elpi__13) =
              (fun ~depth h c s t -> elpi_embed_value ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__11 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_value_Pairc [elpi__14; elpi__15]),
              (List.concat [elpi__12; elpi__13]))
    and elpi_readback_value :
      'c 'csts . (value, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.Const elpi__hd when
            elpi__hd == elpi_constant_constructor_value_Nullc ->
            (elpi__state, Null, [])
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_value_Numberc ->
            let (elpi__state, elpi__2, elpi__1) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | [] -> (elpi__state, (Number elpi__2), (List.concat [elpi__1]))
             | _ ->
                 Elpi.API.Error.error ~component:"ppx_elpi"
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_value_Numberc)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_value_Pairc ->
            let (elpi__state, elpi__6, elpi__5) =
              (fun ~depth h c s t -> elpi_readback_value ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | elpi__3::[] ->
                 let (elpi__state, elpi__3, elpi__4) =
                   (fun ~depth h c s t -> elpi_readback_value ~depth h c s t)
                     ~depth:elpi__depth elpi__hyps elpi__constraints
                     elpi__state elpi__3 in
                 (elpi__state, (Pair (elpi__6, elpi__3)),
                   (List.concat [elpi__5; elpi__4]))
             | _ ->
                 Elpi.API.Error.error ~component:"ppx_elpi"
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_value_Pairc)))
        | _ ->
            Elpi.API.Error.error ~component:"ppx_elpi"
              (Format.asprintf "Not a constructor of type %s: %a" "value"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and value : 'c 'csts . (value, 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "value" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:14 ~variant:0
               ~ty:kind ~name:"val.null" ~doc:"Null" ~args:[];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:14 ~variant:0
               ~ty:kind ~name:"val.number" ~doc:"Number"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:14 ~variant:0
               ~ty:kind ~name:"pair-of-values" ~doc:"Pair"
               ~args:[Elpi.API.ContextualConversion.TyName
                        elpi_constant_type_value;
                     Elpi.API.ContextualConversion.TyName
                       elpi_constant_type_value]);
        pp = pp_value;
        embed = elpi_embed_value;
        readback = elpi_readback_value
      }
    let elpi_value = Elpi.API.BuiltIn.MLDataC value
    let elpi__value__deep_copy =
      "func value.copy value -> value.\nvalue.copy val.null val.null.\nvalue.copy (val.number A0) (val.number B0) :- (int.copy A0 B0).\nvalue.copy (pair-of-values A0 A1) (pair-of-values B0 B1) :- (value.copy A0 B0), (value.copy A1 B1).\n\n"
    class ctx_for_value (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_value.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_value :
      (Ctx_for_value.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s -> (s, ((new ctx_for_value) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_value; Elpi.API.BuiltIn.LPCode elpi__value__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type point = {
  x: int ;
  y: int }[@@elpi.namespace "geo"][@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let pp_point :
      Ppx_deriving_runtime.Format.formatter ->
        point -> Ppx_deriving_runtime.unit
      =
      ((let open! Ppx_deriving_runtime in
          fun fmt x ->
            Ppx_deriving_runtime.Format.fprintf fmt "@[<2>{ ";
            ((Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ "
                "Test_namespace.x";
              (Ppx_deriving_runtime.Format.fprintf fmt "%d") x.x;
              Ppx_deriving_runtime.Format.fprintf fmt "@]");
             Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
             Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "y";
             (Ppx_deriving_runtime.Format.fprintf fmt "%d") x.y;
             Ppx_deriving_runtime.Format.fprintf fmt "@]");
            Ppx_deriving_runtime.Format.fprintf fmt "@ }@]")
      [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_point : point -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_point x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_point = "point"
    let elpi_constant_type_pointc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_point
    let elpi_constant_constructor_point_point = "geo.point"
    let elpi_constant_constructor_point_pointc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_point_point
    module Ctx_for_point =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_point :
      'c 'csts . (point, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | { x = elpi__20; y = elpi__21 } ->
            let (elpi__state, elpi__24, elpi__22) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__20 in
            let (elpi__state, elpi__25, elpi__23) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__21 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_point_pointc [elpi__24; elpi__25]),
              (List.concat [elpi__22; elpi__23]))
    and elpi_readback_point :
      'c 'csts . (point, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_point_pointc ->
            let (elpi__state, elpi__19, elpi__18) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | elpi__16::[] ->
                 let (elpi__state, elpi__16, elpi__17) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__16 in
                 (elpi__state, { x = elpi__19; y = elpi__16 },
                   (List.concat [elpi__18; elpi__17]))
             | _ ->
                 Elpi.API.Error.error ~component:"ppx_elpi"
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_point_pointc)))
        | _ ->
            Elpi.API.Error.error ~component:"ppx_elpi"
              (Format.asprintf "Not a constructor of type %s: %a" "point"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and point : 'c 'csts . (point, 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "point" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:9 ~variant:0
               ~ty:kind ~name:"geo.point" ~doc:"point"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty]);
        pp = pp_point;
        embed = elpi_embed_point;
        readback = elpi_readback_point
      }
    let elpi_point = Elpi.API.BuiltIn.MLDataC point
    let elpi__point__deep_copy =
      "func point.copy point -> point.\npoint.copy (geo.point A0 A1) (geo.point B0 B1) :- (int.copy A0 B0), (int.copy A1 B1).\n\n"
    class ctx_for_point (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_point.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_point :
      (Ctx_for_point.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s -> (s, ((new ctx_for_point) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_point; Elpi.API.BuiltIn.LPCode elpi__point__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let program =
  {|
main :-
  value.copy (pair-of-values val.null (val.number 1)) X,
  X = pair-of-values val.null (val.number 1),
  point.copy (geo.point 1 2) (geo.point 1 2).
|}
let () = Ppx_tests_lib.run_program builtin program
