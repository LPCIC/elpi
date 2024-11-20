let elpi_stuff = ref []
let pp_simple _ _ _ = ()
type 'a simple = ('a * int)[@@deriving elpi { declaration = elpi_stuff }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_simple = "simple"
    let elpi_constant_type_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_simple
    module Ctx_for_simple =
      struct
        class type t = object inherit Elpi.API.ContextualConversion.ctx end
      end
    let rec elpi_embed_simple :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, #Ctx_for_simple.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding ->
          ('elpi__param__a simple, #Ctx_for_simple.t as 'c, 'csts)
            Elpi.API.ContextualConversion.embedding
      =
      fun elpi_embed_elpi__param__a ->
        fun ~depth ->
          fun h ->
            fun c ->
              fun s ->
                fun t ->
                  (Elpi.Builtin.PPX.embed_pair elpi_embed_elpi__param__a
                     Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.embed)
                    ~depth h c s t
    and elpi_readback_simple :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, #Ctx_for_simple.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback ->
          ('elpi__param__a simple, #Ctx_for_simple.t as 'c, 'csts)
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
                     Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.readback)
                    ~depth h c s t
    and simple :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, #Ctx_for_simple.t as 'c, 'csts)
          Elpi.API.ContextualConversion.t ->
          ('elpi__param__a simple, #Ctx_for_simple.t as 'c, 'csts)
            Elpi.API.ContextualConversion.t
      =
      fun elpi__param__a ->
        let kind =
          Elpi.API.ContextualConversion.TyApp
            ("simple", (elpi__param__a.Elpi.API.ContextualConversion.ty), []) in
        {
          Elpi.API.ContextualConversion.ty = kind;
          pp_doc =
            (fun fmt ->
               fun () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:"simple"; ());
          pp = (pp_simple elpi__param__a.pp);
          embed =
            (elpi_embed_simple
               elpi__param__a.Elpi.API.ContextualConversion.embed);
          readback =
            (elpi_readback_simple
               elpi__param__a.Elpi.API.ContextualConversion.readback)
        }
    let elpi_simple =
      let elpi__param__a = Elpi.API.BuiltInContextualData.polyA0 in
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           (("(" ^ ("simple" ^ (" " ^ ("A0" ^ ")")))) ^
              (" " ^
                 (((let open Elpi.API.PPX.Doc in show_ty_ast ~prec:AppArg) @@
                     (Elpi.Builtin.PPX.pair elpi__param__a
                        Elpi.API.BuiltInContextualData.int).Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "simple")))))
    class ctx_for_simple (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_simple.t =
      object (_) inherit  ((Elpi.API.ContextualConversion.ctx) h) end
    let (in_ctx_for_simple :
      (Ctx_for_simple.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_simple) h s), c, (List.concat []))
    let () = elpi_stuff := ((!elpi_stuff) @ [elpi_simple])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
open Elpi.API
let x :
  'a 'c 'csts .
    ('a, 'c, 'csts) ContextualConversion.t ->
      ('a simple, 'c, 'csts) ContextualConversion.t
  = simple
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let _elpi = Setup.init ~builtins:[builtin] () in
  BuiltIn.document_file builtin; exit 0
;;main ()
