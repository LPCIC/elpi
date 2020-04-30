let elpi_stuff = ref []
let pp_simple _ _ _ = ()
type 'a simple = ('a * int)[@@deriving elpi { declaration = elpi_stuff }]
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
      'elpi__param__a 'c .
        ('elpi__param__a, 'c) Elpi.API.Conversion.embedding ->
          ('elpi__param__a simple, #Ctx_for_simple.t as 'c)
            Elpi.API.Conversion.embedding
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
      'elpi__param__a 'c .
        ('elpi__param__a, 'c) Elpi.API.Conversion.readback ->
          ('elpi__param__a simple, #Ctx_for_simple.t as 'c)
            Elpi.API.Conversion.readback
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
      'elpi__param__a 'c .
        ('elpi__param__a, 'c) Elpi.API.Conversion.t ->
          ('elpi__param__a simple, #Ctx_for_simple.t as 'c)
            Elpi.API.Conversion.t
      =
      fun elpi__param__a ->
        let kind =
          Elpi.API.Conversion.TyApp
            ("simple", (elpi__param__a.Elpi.API.Conversion.ty), []) in
        {
          Elpi.API.Conversion.ty = kind;
          pp_doc =
            (fun fmt ->
               fun () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:"simple"; ());
          pp = (pp_simple elpi__param__a.pp);
          embed =
            (elpi_embed_simple elpi__param__a.Elpi.API.Conversion.embed);
          readback =
            (elpi_readback_simple elpi__param__a.Elpi.API.Conversion.readback)
        }
    let elpi_simple =
      let elpi__param__a = Elpi.API.BuiltInData.poly (Printf.sprintf "A%d" 0) in
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           (("(" ^ ("simple" ^ (" " ^ ("A0" ^ ")")))) ^
              (" " ^
                 (((Elpi.API.PPX.Doc.show_ty_ast ~outer:false) @@
                     (Elpi.Builtin.pair elpi__param__a
                        Elpi.API.BuiltInData.int).Elpi.API.Conversion.ty)
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
let x : 'c . ('a, 'c) Conversion.t -> ('a simple, 'c) Conversion.t = simple
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
