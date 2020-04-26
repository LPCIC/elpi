let elpi_stuff = ref []
let pp_simple _ _ _ = ()
type 'a simple = ('a * int)[@@deriving elpi { append = elpi_stuff }]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_simple = "simple"
    let elpi_constant_type_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_simple
    let rec elpi_embed_simple :
      'elpi__param__a 'elpi__param__poly_hyps 'elpi__param__poly_csts .
        ('elpi__param__a, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.embedding ->
          ('elpi__param__a simple, 'elpi__param__poly_hyps,
            'elpi__param__poly_csts) Elpi.API.ContextualConversion.embedding
      =
      fun elpi_embed_elpi__param__a ->
        fun ~depth ->
          fun h ->
            fun c ->
              fun s ->
                fun t ->
                  (Elpi.Builtin.PPX.embed_pair elpi_embed_elpi__param__a
                     Elpi.API.PPX.embed_int) ~depth h c s t
    let rec elpi_readback_simple :
      'elpi__param__a 'elpi__param__poly_hyps 'elpi__param__poly_csts .
        ('elpi__param__a, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.readback ->
          ('elpi__param__a simple, 'elpi__param__poly_hyps,
            'elpi__param__poly_csts) Elpi.API.ContextualConversion.readback
      =
      fun elpi_readback_elpi__param__a ->
        fun ~depth ->
          fun h ->
            fun c ->
              fun s ->
                fun t ->
                  (Elpi.Builtin.PPX.readback_pair
                     elpi_readback_elpi__param__a Elpi.API.PPX.readback_int)
                    ~depth h c s t
    let simple :
      'elpi__param__a 'elpi__param__poly_hyps 'elpi__param__poly_csts .
        ('elpi__param__a, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.t ->
          ('elpi__param__a simple, 'elpi__param__poly_hyps,
            'elpi__param__poly_csts) Elpi.API.ContextualConversion.t
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
      let elpi__param__a =
        Elpi.API.ContextualConversion.(!>) @@
          (Elpi.API.BuiltInData.poly (Printf.sprintf "A%d" 0)) in
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           (("(" ^ ("simple" ^ (" " ^ ("A0" ^ ")")))) ^
              (" " ^
                 (((Elpi.API.PPX.Doc.show_ty_ast ~outer:false) @@
                     (Elpi.API.ContextualConversion.(!>>>) Elpi.Builtin.pair
                        elpi__param__a
                        (Elpi.API.ContextualConversion.(!>)
                           Elpi.API.BuiltInData.int)).Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "simple")))))
    let () =
      elpi_stuff :=
        ((!elpi_stuff) @
           ([elpi_simple] @
              [Elpi.API.BuiltIn.LPCode
                 (String.concat "\n"
                    ["pred map.simple i:(X0 -> Y0 -> prop),  i:simple X0, o:simple Y0.";
                    Printf.sprintf "map.%s %sA B :- %s." "simple" "F0 "
                      ("(" ^
                         ((Printf.sprintf "(ppx.map.pair %s %s)" "F0" "(=)")
                            ^ (" " ^ ("A" ^ (" " ^ ("B" ^ ")"))))))])]))
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
open Elpi.API
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
