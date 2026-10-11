let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type t1 =
  | A of int [@elpi.variant 1][@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_t1
      : Ppx_deriving_runtime.Format.formatter ->
          t1 -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt ->
            function
            | A a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_variant.A@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])"))
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_t1 : t1 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_t1 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_t1 = "t1"
    let elpi_constant_type_t1c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_t1
    let elpi_constant_constructor_t1_A = "a"
    let elpi_constant_constructor_t1_Ac =
      Elpi.API.RawData.Constants.declare_global_symbol ~variant:1
        elpi_constant_constructor_t1_A
    module Ctx_for_t1 =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_t1 :
      'c 'csts . (t1, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | A elpi__3 ->
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
                         elpi_constant_constructor_t1_Ac [elpi__5]),
                      (List.concat [elpi__4]))
    and elpi_readback_t1 :
      'c 'csts . (t1, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_t1_Ac ->
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
                         (elpi__state, (A elpi__2), (List.concat [elpi__1]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_t1_Ac)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "t1" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and t1 : 'c 'csts . (t1, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "t1" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:1
                 ~ty:kind ~name:"a" ~doc:"A"
                 ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty]);
        pp = pp_t1;
        embed = elpi_embed_t1;
        readback = elpi_readback_t1
      }
    let elpi_t1 = Elpi.API.BuiltIn.MLDataC t1
    let elpi__t1__deep_copy =
      "func t1.copy t1 -> t1.\nt1.copy (a A0) (a B0) :- (int.copy A0 B0).\n\n"
    class ctx_for_t1 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_t1.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_t1 :
      (Ctx_for_t1.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_t1) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_t1; Elpi.API.BuiltIn.LPCode elpi__t1__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type t2 =
  | A of string [@elpi.variant 2][@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_t2
      : Ppx_deriving_runtime.Format.formatter ->
          t2 -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt ->
            function
            | A a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_variant.A@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])"))
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_t2 : t2 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_t2 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_t2 = "t2"
    let elpi_constant_type_t2c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_t2
    let elpi_constant_constructor_t2_A = "a"
    let elpi_constant_constructor_t2_Ac =
      Elpi.API.RawData.Constants.declare_global_symbol ~variant:2
        elpi_constant_constructor_t2_A
    module Ctx_for_t2 =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_t2 :
      'c 'csts . (t2, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | A elpi__8 ->
                    let (elpi__state, elpi__10, elpi__9) =
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
                         elpi_constant_constructor_t2_Ac [elpi__10]),
                      (List.concat [elpi__9]))
    and elpi_readback_t2 :
      'c 'csts . (t2, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_t2_Ac ->
                    let (elpi__state, elpi__7, elpi__6) =
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
                         (elpi__state, (A elpi__7), (List.concat [elpi__6]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_t2_Ac)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "t2" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and t2 : 'c 'csts . (t2, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "t2" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:2
                 ~ty:kind ~name:"a" ~doc:"A"
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty]);
        pp = pp_t2;
        embed = elpi_embed_t2;
        readback = elpi_readback_t2
      }
    let elpi_t2 = Elpi.API.BuiltIn.MLDataC t2
    let elpi__t2__deep_copy =
      "func t2.copy t2 -> t2.\nt2.copy (a A0) (a B0) :- (string.copy A0 B0).\n\n"
    class ctx_for_t2 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_t2.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_t2 :
      (Ctx_for_t2.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_t2) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_t2; Elpi.API.BuiltIn.LPCode elpi__t2__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let program =
  {|
main :-
  t1.copy (a 1) X, X = a 1,
  t2.copy (a "s") Y, Y = a "s".
|}
let () = Ppx_tests_lib.run_program builtin program
