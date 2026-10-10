let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type simple =
  | K1 of {
  f: int ;
  g: bool } 
  | K2 of {
  f2: bool } [@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_simple
      : Ppx_deriving_runtime.Format.formatter ->
          simple -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt ->
            function
            | K1 { f = af; g = ag } ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "@[<2>Test_simple_adt_record.K1 {@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "f";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%d") af;
                   Ppx_deriving_runtime.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "g";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%B") ag;
                  Ppx_deriving_runtime.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime.Format.fprintf fmt "@]}")
            | K2 { f2 = af2 } ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "@[<2>Test_simple_adt_record.K2 {@,";
                 (Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "f2";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%B") af2;
                  Ppx_deriving_runtime.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime.Format.fprintf fmt "@]}"))
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_simple : simple -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_simple x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_simple = "simple"
    let elpi_constant_type_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_simple
    let elpi_constant_constructor_simple_K1 = "k1"
    let elpi_constant_constructor_simple_K1c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_simple_K1
    let elpi_constant_constructor_simple_K2 = "k2"
    let elpi_constant_constructor_simple_K2c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_simple_K2
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
                | K1 { f = elpi__7; g = elpi__8 } ->
                    let (elpi__state, elpi__11, elpi__9) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__7 in
                    let (elpi__state, elpi__12, elpi__10) =
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
                         elpi_constant_constructor_simple_K1c
                         [elpi__11; elpi__12]),
                      (List.concat [elpi__9; elpi__10]))
                | K2 { f2 = elpi__13 } ->
                    let (elpi__state, elpi__15, elpi__14) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__13 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_simple_K2c [elpi__15]),
                      (List.concat [elpi__14]))
    and elpi_readback_simple :
      'c 'csts . (simple, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_simple_K1c ->
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
                         (elpi__state, (K1 { f = elpi__4; g = elpi__1 }),
                           (List.concat [elpi__3; elpi__2]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_simple_K1c)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_simple_K2c ->
                    let (elpi__state, elpi__6, elpi__5) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | [] ->
                         (elpi__state, (K2 { f2 = elpi__6 }),
                           (List.concat [elpi__5]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_simple_K2c)))
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
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
                 ~ty:kind ~name:"k1" ~doc:"K1"
                 ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                       Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
                 ~ty:kind ~name:"k2" ~doc:"K2"
                 ~args:[Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty]);
        pp = pp_simple;
        embed = elpi_embed_simple;
        readback = elpi_readback_simple
      }
    let elpi_simple = Elpi.API.BuiltIn.MLDataC simple
    let elpi__simple__deep_copy =
      "func simple.copy simple -> simple.\nsimple.copy (k1 A0 A1) (k1 B0 B1) :- (int.copy A0 B0), (bool.copy A1 B1).\nsimple.copy (k2 A0) (k2 B0) :- (bool.copy A0 B0).\n\n"
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
