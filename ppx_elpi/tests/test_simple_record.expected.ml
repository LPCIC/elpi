let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type simple = {
  f: int ;
  g: bool }[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_simple
      : Ppx_deriving_runtime.Format.formatter ->
          simple -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime.Format.fprintf fmt "@[<2>{ ";
              ((Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ "
                  "Test_simple_record.f";
                (Ppx_deriving_runtime.Format.fprintf fmt "%d") x.f;
                Ppx_deriving_runtime.Format.fprintf fmt "@]");
               Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "g";
               (Ppx_deriving_runtime.Format.fprintf fmt "%B") x.g;
               Ppx_deriving_runtime.Format.fprintf fmt "@]");
              Ppx_deriving_runtime.Format.fprintf fmt "@ }@]")
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_simple : simple -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_simple x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_simple = "simple"
    let elpi_constant_type_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_simple
    let elpi_constant_constructor_simple_simple = "simple"
    let elpi_constant_constructor_simple_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_simple_simple
    module Ctx_for_simple =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_simple :
      'c 'csts . (simple, 'c, 'csts) Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | { f = elpi__5; g = elpi__6 } ->
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
                                 Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__6 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_simple_simplec
                         [elpi__9; elpi__10]),
                      (List.concat [elpi__7; elpi__8]))
    and elpi_readback_simple :
      'c 'csts . (simple, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_simple_simplec ->
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
                                      Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__1 in
                         (elpi__state, { f = elpi__4; g = elpi__1 },
                           (List.concat [elpi__3; elpi__2]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_simple_simplec)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "simple" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and simple :
      'c 'csts . (simple, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "simple" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:6 ~variant:0
                 ~ty:kind ~name:"simple" ~doc:"simple"
                 ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                       Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty]);
        pp = pp_simple;
        embed = elpi_embed_simple;
        readback = elpi_readback_simple
      }
    let elpi_simple = Elpi.API.BuiltIn.MLDataC simple
    let elpi__simple__deep_copy =
      "func simple.copy simple -> simple.\nsimple.copy (simple A0 A1) (simple B0 B1) :- (int.copy A0 B0), (bool.copy A1 B1).\n\n"
    class ctx_for_simple (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_simple.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_simple :
      (Ctx_for_simple.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_simple) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_simple; Elpi.API.BuiltIn.LPCode elpi__simple__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let () = Ppx_tests_lib.check_declarations builtin
