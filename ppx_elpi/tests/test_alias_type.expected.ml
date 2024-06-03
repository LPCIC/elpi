let elpi_stuff = ref []
let pp_simple _ _ = ()
type simple = int[@@deriving elpi { declaration = elpi_stuff }]
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
      'c 'csts .
        (simple, #Ctx_for_simple.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.embed
                  ~depth h c s t
    and elpi_readback_simple :
      'c 'csts .
        (simple, #Ctx_for_simple.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.readback
                  ~depth h c s t
    and simple :
      'c 'csts .
        (simple, #Ctx_for_simple.t as 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "simple" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:"simple"; ());
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
                     Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.ty)
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
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let _elpi = Setup.init ~builtins:[builtin] () in
  BuiltIn.document_file builtin; exit 0
;;main ()
