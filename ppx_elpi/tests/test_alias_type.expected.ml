let elpi_stuff = ref []
let pp_simple _ _ = ()
type simple = int[@@deriving elpi { declaration = elpi_stuff }]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_simple = "simple"
    let elpi_constant_type_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_simple
    module Ctx_for_simple =
      struct class type t = object inherit Elpi.API.Conversion.ctx end end
    let rec elpi_embed_simple :
      'c . (simple, #Ctx_for_simple.t as 'c) Elpi.API.Conversion.embedding =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> fun t -> Elpi.API.PPX.embed_int ~depth h c s t
    let rec elpi_readback_simple :
      'c . (simple, #Ctx_for_simple.t as 'c) Elpi.API.Conversion.readback =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> fun t -> Elpi.API.PPX.readback_int ~depth h c s t
    let simple : 'c . (simple, #Ctx_for_simple.t as 'c) Elpi.API.Conversion.t
      =
      let kind = Elpi.API.Conversion.TyName "simple" in
      {
        Elpi.API.Conversion.ty = kind;
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
                 (((Elpi.API.PPX.Doc.show_ty_ast ~outer:false) @@
                     Elpi.API.BuiltInData.int.Elpi.API.Conversion.ty)
                    ^ (". % " ^ "simple")))))
    class ctx_for_simple (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_simple.t =
      object (_) inherit  ((Elpi.API.Conversion.ctx) h) end
    let (in_ctx_for_simple :
      Ctx_for_simple.t Elpi.API.Conversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_simple) h s), (List.concat []))
    let () = elpi_stuff := ((!elpi_stuff) @ [elpi_simple])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
open Elpi.API
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
