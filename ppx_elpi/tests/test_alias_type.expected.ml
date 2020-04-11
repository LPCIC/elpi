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
    let rec elpi_embed_simple :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (simple, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> fun t -> Elpi.API.PPX.embed_int ~depth h c s t
    let rec elpi_readback_simple :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (simple, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> fun t -> Elpi.API.PPX.readback_int ~depth h c s t
    let simple :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (simple, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
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
                 (((Elpi.API.PPX.Doc.show_ty_ast ~outer:false) @@
                     (Elpi.API.ContextualConversion.(!>)
                        Elpi.API.BuiltInData.int).Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "simple")))))
    let () = elpi_stuff := ((!elpi_stuff) @ [elpi_simple])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
open Elpi.API
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
