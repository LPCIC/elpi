let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type 'a simple =
  | A 
  | B of int 
  | C of 'a list * int [@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_simple
      : 'a .
          (Ppx_deriving_runtime.Format.formatter ->
             'a -> Ppx_deriving_runtime.unit)
            ->
            Ppx_deriving_runtime.Format.formatter ->
              'a simple -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun poly_a ->
            fun fmt ->
              function
              | A ->
                  Ppx_deriving_runtime.Format.pp_print_string fmt
                    "Test_poly_adt.A"
              | B a0 ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_poly_adt.B@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt "@])")
              | C (a0, a1) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_poly_adt.C (@,";
                   (((fun x ->
                        Ppx_deriving_runtime.Format.fprintf fmt "@[<2>[";
                        ignore
                          (List.fold_left
                             (fun sep ->
                                fun x ->
                                  if sep
                                  then
                                    Ppx_deriving_runtime.Format.fprintf fmt
                                      ";@ ";
                                  (poly_a fmt) x;
                                  true) false x);
                        Ppx_deriving_runtime.Format.fprintf fmt "@,]@]")) a0;
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (Ppx_deriving_runtime.Format.fprintf fmt "%d") a1);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_simple :
      'a .
        (Ppx_deriving_runtime.Format.formatter ->
           'a -> Ppx_deriving_runtime.unit)
          -> 'a simple -> Ppx_deriving_runtime.string
      =
      fun poly_a ->
        fun x ->
          Ppx_deriving_runtime.Format.asprintf "%a" (pp_simple poly_a) x
    [@@ocaml.warning "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_simple = "simple"
    let elpi_constant_type_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_simple
    let elpi_constant_constructor_simple_A = "a"
    let elpi_constant_constructor_simple_Ac =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_simple_A
    let elpi_constant_constructor_simple_B = "b"
    let elpi_constant_constructor_simple_Bc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_simple_B
    let elpi_constant_constructor_simple_C = "c"
    let elpi_constant_constructor_simple_Cc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_simple_C
    module Ctx_for_simple =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_simple :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.embedding
          ->
          ('elpi__param__a simple, 'c, 'csts)
            Elpi.API.ContextualConversion.embedding
      =
      fun elpi_embed_elpi__param__a ->
        fun ~depth:elpi__depth ->
          fun elpi__hyps ->
            fun elpi__constraints ->
              fun elpi__state ->
                fun elpi__fun_arg ->
                  match elpi__fun_arg with
                  | A ->
                      (elpi__state,
                        (Elpi.API.RawData.mkAppGlobalL
                           elpi_constant_constructor_simple_Ac []),
                        (List.concat []))
                  | B elpi__7 ->
                      let (elpi__state, elpi__9, elpi__8) =
                        (fun ~depth ->
                           fun h ->
                             fun c ->
                               fun s ->
                                 fun t ->
                                   Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                     ~depth h c s t) ~depth:elpi__depth
                          elpi__hyps elpi__constraints elpi__state elpi__7 in
                      (elpi__state,
                        (Elpi.API.RawData.mkAppGlobalL
                           elpi_constant_constructor_simple_Bc [elpi__9]),
                        (List.concat [elpi__8]))
                  | C (elpi__10, elpi__11) ->
                      let (elpi__state, elpi__14, elpi__12) =
                        (fun ~depth ->
                           fun h ->
                             fun c ->
                               fun s ->
                                 fun t ->
                                   (let embed = elpi_embed_elpi__param__a in
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
                          elpi__state elpi__10 in
                      let (elpi__state, elpi__15, elpi__13) =
                        (fun ~depth ->
                           fun h ->
                             fun c ->
                               fun s ->
                                 fun t ->
                                   Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                                     ~depth h c s t) ~depth:elpi__depth
                          elpi__hyps elpi__constraints elpi__state elpi__11 in
                      (elpi__state,
                        (Elpi.API.RawData.mkAppGlobalL
                           elpi_constant_constructor_simple_Cc
                           [elpi__14; elpi__15]),
                        (List.concat [elpi__12; elpi__13]))
    and elpi_readback_simple :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.readback
          ->
          ('elpi__param__a simple, 'c, 'csts)
            Elpi.API.ContextualConversion.readback
      =
      fun elpi_readback_elpi__param__a ->
        fun ~depth:elpi__depth ->
          fun elpi__hyps ->
            fun elpi__constraints ->
              fun elpi__state ->
                fun elpi__x ->
                  match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                  | Elpi.API.RawData.Const elpi__hd when
                      elpi__hd == elpi_constant_constructor_simple_Ac ->
                      (elpi__state, A, [])
                  | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                      elpi__hd == elpi_constant_constructor_simple_Bc ->
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
                           (elpi__state, (B elpi__2),
                             (List.concat [elpi__1]))
                       | _ ->
                           Elpi.API.Utils.type_error
                             ("Not enough arguments to constructor: " ^
                                (Elpi.API.RawData.Constants.show
                                   elpi_constant_constructor_simple_Bc)))
                  | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                      elpi__hd == elpi_constant_constructor_simple_Cc ->
                      let (elpi__state, elpi__6, elpi__5) =
                        (fun ~depth ->
                           fun h ->
                             fun c ->
                               fun s ->
                                 fun t ->
                                   (let readback =
                                      elpi_readback_elpi__param__a in
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
                       | elpi__3::[] ->
                           let (elpi__state, elpi__3, elpi__4) =
                             (fun ~depth ->
                                fun h ->
                                  fun c ->
                                    fun s ->
                                      fun t ->
                                        Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                                          ~depth h c s t) ~depth:elpi__depth
                               elpi__hyps elpi__constraints elpi__state
                               elpi__3 in
                           (elpi__state, (C (elpi__6, elpi__3)),
                             (List.concat [elpi__5; elpi__4]))
                       | _ ->
                           Elpi.API.Utils.type_error
                             ("Not enough arguments to constructor: " ^
                                (Elpi.API.RawData.Constants.show
                                   elpi_constant_constructor_simple_Cc)))
                  | _ ->
                      Elpi.API.Utils.type_error
                        (Format.asprintf "Not a constructor of type %s: %a"
                           "simple" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and simple :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.t ->
          ('elpi__param__a simple, 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      fun elpi__param__a ->
        let kind =
          Elpi.API.ContextualConversion.TyApp
            ("simple", (elpi__param__a.Elpi.API.ContextualConversion.ty), []) in
        {
          Elpi.API.ContextualConversion.ty = kind;
          pp_doc =
            (fun fmt ->
               fun () ->
                 Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
                 Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:0
                   ~ty:kind ~name:"a" ~doc:"A" ~args:[];
                 Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:0
                   ~ty:kind ~name:"b" ~doc:"B"
                   ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty];
                 Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:0
                   ~ty:kind ~name:"c" ~doc:"C"
                   ~args:[Elpi.API.ContextualConversion.TyApp
                            ("list",
                              (elpi__param__a.Elpi.API.ContextualConversion.ty),
                              []);
                         Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty]);
          pp = (pp_simple elpi__param__a.pp);
          embed =
            (elpi_embed_simple
               elpi__param__a.Elpi.API.ContextualConversion.embed);
          readback =
            (elpi_readback_simple
               elpi__param__a.Elpi.API.ContextualConversion.readback)
        }
    let elpi_simple =
      Elpi.API.BuiltIn.MLDataC (simple (Elpi.API.BuiltInData.polyC "A"))
    let elpi__simple__deep_copy =
      "func simple.copy (func X0 -> Y0), simple X0 -> simple Y0.\nsimple.copy _ a a.\nsimple.copy _ (b A0) (b B0) :- (int.copy A0 B0).\nsimple.copy F0 (c A0 A1) (c B0 B1) :- ((list.copy F0) A0 B0), (int.copy A1 B1).\n\n"
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
let simple :
  'a 'c 'csts .
    ('a, #PPX.ctx as 'c, 'csts) ContextualConversion.t ->
      ('a simple, #PPX.ctx as 'c, 'csts) ContextualConversion.t
  = simple
let t2 : (int simple, PPX.ctx, Data.constraints) ContextualConversion.t =
  simple BuiltInData.intC
class type my_context_subclass =
  object inherit PPX.ctx method  foobar : bool end
let t3
  : (float simple, my_context_subclass, Data.constraints)
      ContextualConversion.t
  = simple BuiltInData.floatC
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let () = Ppx_tests_lib.check_declarations builtin
