let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type simple = int[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_simple
      : Ppx_deriving_runtime.Format.formatter ->
          simple -> Ppx_deriving_runtime.unit
      =
      ((let open! ((Ppx_deriving_runtime)[@ocaml.warning "-A"]) in
          fun fmt -> Ppx_deriving_runtime.Format.fprintf fmt "%d")
      [@ocaml.warning "-39"][@ocaml.warning "-A"])
    and show_simple : simple -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_simple x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_simple = "simple"
    let elpi_constant_type_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_simple
    module Ctx_for_simple =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_simple :
      'c 'csts . (simple, 'c, 'csts) Elpi.API.ContextualConversion.embedding
      =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                  ~depth h c s t
    and elpi_readback_simple :
      'c 'csts . (simple, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                  ~depth h c s t
    and simple :
      'c 'csts . (simple, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "simple" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt -> fun () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:""; ());
        pp = pp_simple;
        embed = elpi_embed_simple;
        readback = elpi_readback_simple
      }
    let elpi_simple =
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           ("simple" ^
              (" " ^
                 (((let open Elpi.API.PPX.Doc in show_ty_ast ~prec:AppArg) @@
                     Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "simple")))))
    let elpi__simple__deep_copy =
      "func simple.copy simple -> simple.\nsimple.copy A B :- (int.copy A B)."
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
