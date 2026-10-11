let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
let pp_simple _ _ = ()
type simple[@@elpi.opaque
             {
               OpaqueData.name = "simple";
               doc = "";
               pp = (fun fmt -> fun _ -> Format.fprintf fmt "<simple>");
               compare = Stdlib.compare;
               hash = Hashtbl.hash;
               hconsed = false;
               constants = []
             }][@@deriving elpi { declaration }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_simple = "simple"
    let elpi_constant_type_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_simple
    let elpi_opaque_data_decl_simple =
      Elpi.API.OpaqueData.declare
        {
          OpaqueData.name = "simple";
          doc = "";
          pp = (fun fmt -> fun _ -> Format.fprintf fmt "<simple>");
          compare = Stdlib.compare;
          hash = Hashtbl.hash;
          hconsed = false;
          constants = []
        }
    module Ctx_for_simple =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let simple : 'c . (simple, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let { Elpi.API.Conversion.embed = embed; readback; ty; pp_doc; pp } =
        elpi_opaque_data_decl_simple in
      let embed ~depth  _ _ s t = embed ~depth s t in
      let readback ~depth  _ _ s t = readback ~depth s t in
      { Elpi.API.ContextualConversion.embed = embed; readback; ty; pp_doc; pp
      }
    let elpi_embed_simple = simple.Elpi.API.ContextualConversion.embed
    let elpi_readback_simple = simple.Elpi.API.ContextualConversion.readback
    let elpi_simple = Elpi.API.BuiltIn.MLDataC simple
    let elpi__simple__deep_copy =
      "func simple.copy simple -> simple.\nsimple.copy X X.\n"
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
let simple : 'h . (simple, #PPX.ctx as 'h, 'c) ContextualConversion.t =
  simple
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let () = Ppx_tests_lib.check_declarations builtin
