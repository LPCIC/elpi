let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type id = string[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_id
      : Ppx_deriving_runtime.Format.formatter ->
          id -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt -> Ppx_deriving_runtime.Format.fprintf fmt "%S")
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_id : id -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_id x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_id = "id"
    let elpi_constant_type_idc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_id
    module Ctx_for_id =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_id :
      'c 'csts . (id, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                  ~depth h c s t
    and elpi_readback_id :
      'c 'csts . (id, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                  ~depth h c s t
    and id : 'c 'csts . (id, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "id" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt -> fun () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:""; ());
        pp = pp_id;
        embed = elpi_embed_id;
        readback = elpi_readback_id
      }
    let elpi_id =
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           ("id" ^
              (" " ^
                 (((let open Elpi.API.PPX.Doc in show_ty_ast ~prec:AppArg) @@
                     Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "id")))))
    let elpi__id__deep_copy =
      "func id.copy id -> id.\nid.copy A B :- (string.copy A B)."
    class ctx_for_id (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_id.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_id :
      (Ctx_for_id.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_id) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_id; Elpi.API.BuiltIn.LPCode elpi__id__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type 'a counted = ('a * int)[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_counted
      : 'a .
          (Ppx_deriving_runtime.Format.formatter ->
             'a -> Ppx_deriving_runtime.unit)
            ->
            Ppx_deriving_runtime.Format.formatter ->
              'a counted -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun poly_a ->
            fun fmt ->
              fun (a0, a1) ->
                Ppx_deriving_runtime.Format.fprintf fmt "(@[";
                ((poly_a fmt) a0;
                 Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a1);
                Ppx_deriving_runtime.Format.fprintf fmt "@])")
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_counted :
      'a .
        (Ppx_deriving_runtime.Format.formatter ->
           'a -> Ppx_deriving_runtime.unit)
          -> 'a counted -> Ppx_deriving_runtime.string
      =
      fun poly_a ->
        fun x ->
          Ppx_deriving_runtime.Format.asprintf "%a" (pp_counted poly_a) x
    [@@ocaml.warning "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_counted = "counted"
    let elpi_constant_type_countedc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_counted
    module Ctx_for_counted =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_counted :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.embedding
          ->
          ('elpi__param__a counted, 'c, 'csts)
            Elpi.API.ContextualConversion.embedding
      =
      fun elpi_embed_elpi__param__a ->
        fun ~depth ->
          fun h ->
            fun c ->
              fun s ->
                fun t ->
                  (Elpi.Builtin.PPX.embed_pair elpi_embed_elpi__param__a
                     Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed)
                    ~depth h c s t
    and elpi_readback_counted :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.readback
          ->
          ('elpi__param__a counted, 'c, 'csts)
            Elpi.API.ContextualConversion.readback
      =
      fun elpi_readback_elpi__param__a ->
        fun ~depth ->
          fun h ->
            fun c ->
              fun s ->
                fun t ->
                  (Elpi.Builtin.PPX.readback_pair
                     elpi_readback_elpi__param__a
                     Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback)
                    ~depth h c s t
    and counted :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.t ->
          ('elpi__param__a counted, 'c, 'csts)
            Elpi.API.ContextualConversion.t
      =
      fun elpi__param__a ->
        let kind =
          Elpi.API.ContextualConversion.TyApp
            ("counted", (elpi__param__a.Elpi.API.ContextualConversion.ty),
              []) in
        {
          Elpi.API.ContextualConversion.ty = kind;
          pp_doc =
            (fun fmt -> fun () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:""; ());
          pp = (pp_counted elpi__param__a.pp);
          embed =
            (elpi_embed_counted
               elpi__param__a.Elpi.API.ContextualConversion.embed);
          readback =
            (elpi_readback_counted
               elpi__param__a.Elpi.API.ContextualConversion.readback)
        }
    let elpi_counted =
      let elpi__param__a = Elpi.API.BuiltInData.polyC "A" in
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           (("(" ^ ("counted" ^ (" " ^ ("A" ^ ")")))) ^
              (" " ^
                 (((let open Elpi.API.PPX.Doc in show_ty_ast ~prec:AppArg) @@
                     (Elpi.Builtin.PPX.pair elpi__param__a
                        Elpi.API.BuiltInData.intC).Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "counted")))))
    let elpi__counted__deep_copy =
      "func counted.copy (func X0 -> Y0), counted X0 -> counted Y0.\ncounted.copy F0 A B :- ((pair.copy F0 int.copy) A B)."
    class ctx_for_counted (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_counted.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_counted :
      (Ctx_for_counted.t, 'csts) Elpi.API.ContextualConversion.ctx_readback)
      =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_counted) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_counted; Elpi.API.BuiltIn.LPCode elpi__counted__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let pp_secret fmt _ = Format.fprintf fmt "<secret>"
type secret[@@elpi.opaque
             {
               OpaqueData.name = "secret";
               doc = "";
               pp = pp_secret;
               compare = Stdlib.compare;
               hash = Hashtbl.hash;
               hconsed = false;
               constants = []
             }][@@deriving elpi { declaration }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_secret = "secret"
    let elpi_constant_type_secretc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_secret
    let elpi_opaque_data_decl_secret =
      Elpi.API.OpaqueData.declare
        {
          OpaqueData.name = "secret";
          doc = "";
          pp = pp_secret;
          compare = Stdlib.compare;
          hash = Hashtbl.hash;
          hconsed = false;
          constants = []
        }
    module Ctx_for_secret =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let secret : 'c . (secret, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let { Elpi.API.Conversion.embed = embed; readback; ty; pp_doc; pp } =
        elpi_opaque_data_decl_secret in
      let embed ~depth  _ _ s t = embed ~depth s t in
      let readback ~depth  _ _ s t = readback ~depth s t in
      { Elpi.API.ContextualConversion.embed = embed; readback; ty; pp_doc; pp
      }
    let elpi_embed_secret = secret.Elpi.API.ContextualConversion.embed
    let elpi_readback_secret = secret.Elpi.API.ContextualConversion.readback
    let elpi_secret = Elpi.API.BuiltIn.MLDataC secret
    let elpi__secret__deep_copy =
      "func secret.copy secret -> secret.\nsecret.copy X X.\n"
    class ctx_for_secret (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_secret.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_secret :
      (Ctx_for_secret.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_secret) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_secret; Elpi.API.BuiltIn.LPCode elpi__secret__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type entry =
  | E of id * secret * float counted [@@deriving
                                       (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_entry
      : Ppx_deriving_runtime.Format.formatter ->
          entry -> Ppx_deriving_runtime.unit
      =
      ((let __2 = pp_counted
        and __1 = pp_secret
        and __0 = pp_id in
        ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
            fun fmt ->
              function
              | E (a0, a1, a2) ->
                  (Ppx_deriving_runtime.Format.fprintf fmt
                     "(@[<2>Test_copy_aliases_opaque.E (@,";
                   (((__0 fmt) a0;
                     Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                     (__1 fmt) a1);
                    Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                    (__2
                       (fun fmt ->
                          Ppx_deriving_runtime.Format.fprintf fmt "%F") fmt)
                      a2);
                   Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
          [@ocaml.warning "-A"]))
      [@ocaml.warning "-39"])
    and show_entry : entry -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_entry x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_entry = "entry"
    let elpi_constant_type_entryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_entry
    let elpi_constant_constructor_entry_E = "e"
    let elpi_constant_constructor_entry_Ec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_entry_E
    module Ctx_for_entry =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_entry :
      'c 'csts . (entry, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__fun_arg ->
                match elpi__fun_arg with
                | E (elpi__7, elpi__8, elpi__9) ->
                    let (elpi__state, elpi__13, elpi__10) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 id.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__7 in
                    let (elpi__state, elpi__14, elpi__11) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 secret.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__8 in
                    let (elpi__state, elpi__15, elpi__12) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 (counted Elpi.API.BuiltInData.floatC).Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__9 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppGlobalL
                         elpi_constant_constructor_entry_Ec
                         [elpi__13; elpi__14; elpi__15]),
                      (List.concat [elpi__10; elpi__11; elpi__12]))
    and elpi_readback_entry :
      'c 'csts . (entry, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_entry_Ec ->
                    let (elpi__state, elpi__6, elpi__5) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 id.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__1::elpi__2::[] ->
                         let (elpi__state, elpi__1, elpi__3) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      secret.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__1 in
                         let (elpi__state, elpi__2, elpi__4) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      (counted Elpi.API.BuiltInData.floatC).Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state elpi__2 in
                         (elpi__state, (E (elpi__6, elpi__1, elpi__2)),
                           (List.concat [elpi__5; elpi__3; elpi__4]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_entry_Ec)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "entry" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and entry : 'c 'csts . (entry, 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "entry" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:1 ~variant:0
                 ~ty:kind ~name:"e" ~doc:"E"
                 ~args:[id.Elpi.API.ContextualConversion.ty;
                       secret.Elpi.API.ContextualConversion.ty;
                       (counted Elpi.API.BuiltInData.floatC).Elpi.API.ContextualConversion.ty]);
        pp = pp_entry;
        embed = elpi_embed_entry;
        readback = elpi_readback_entry
      }
    let elpi_entry = Elpi.API.BuiltIn.MLDataC entry
    let elpi__entry__deep_copy =
      "func entry.copy entry -> entry.\nentry.copy (e A0 A1 A2) (e B0 B1 B2) :- (id.copy A0 B0), (secret.copy A1 B1), ((counted.copy float.copy) A2 B2).\n\n"
    class ctx_for_entry (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_entry.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let (in_ctx_for_entry :
      (Ctx_for_entry.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_entry) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_entry; Elpi.API.BuiltIn.LPCode elpi__entry__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let () = Ppx_tests_lib.check_declarations builtin
