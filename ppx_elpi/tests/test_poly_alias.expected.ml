let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type 'a simple = ('a * int)[@@deriving (show, (elpi { declaration }))]
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
              fun (a0, a1) ->
                Ppx_deriving_runtime.Format.fprintf fmt "(@[";
                ((poly_a fmt) a0;
                 Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a1);
                Ppx_deriving_runtime.Format.fprintf fmt "@])")
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
        fun ~depth ->
          fun h ->
            fun c ->
              fun s ->
                fun t ->
                  (Elpi.Builtin.PPX.embed_pair elpi_embed_elpi__param__a
                     Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed)
                    ~depth h c s t
    and elpi_readback_simple :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.readback
          ->
          ('elpi__param__a simple, 'c, 'csts)
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
            (fun fmt -> fun () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:""; ());
          pp = (pp_simple elpi__param__a.pp);
          embed =
            (elpi_embed_simple
               elpi__param__a.Elpi.API.ContextualConversion.embed);
          readback =
            (elpi_readback_simple
               elpi__param__a.Elpi.API.ContextualConversion.readback)
        }
    let elpi_simple =
      let elpi__param__a = Elpi.API.BuiltInData.polyC "A" in
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           (("(" ^ ("simple" ^ (" " ^ ("A" ^ ")")))) ^
              (" " ^
                 (((let open Elpi.API.PPX.Doc in show_ty_ast ~prec:AppArg) @@
                     (Elpi.Builtin.PPX.pair elpi__param__a
                        Elpi.API.BuiltInData.intC).Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "simple")))))
    let elpi__simple__deep_copy =
      "func simple.copy (func X0 -> Y0), simple X0 -> simple Y0.\nsimple.copy F0 A B :- ((pair.copy F0 int.copy) A B)."
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
    ('a, 'c, 'csts) ContextualConversion.t ->
      ('a simple, 'c, 'csts) ContextualConversion.t
  = simple
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let () = Ppx_tests_lib.check_declarations builtin
