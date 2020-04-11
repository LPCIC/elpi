let elpi_stuff = ref []
let pp_simple _ _ = ()
type simple[@@deriving elpi { declaration = elpi_stuff }]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_simple = "simple"
    let elpi_constant_type_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_simple
    let (simple : simple Elpi.API.Conversion.t) =
      Elpi.API.OpaqueData.declare
        {
          Elpi.API.OpaqueData.name = "simple";
          doc = "";
          pp = pp_simple;
          compare = Pervasives.compare;
          hash = Hashtbl.hash;
          hconsed = false;
          constants = []
        }
    let elpi_embed_simple ~depth  _ _ s t =
      simple.Elpi.API.Conversion.embed ~depth s t
    let elpi_readback_simple ~depth  _ _ s t =
      simple.Elpi.API.Conversion.readback ~depth s t
    let elpi_simple = Elpi.API.BuiltIn.MLData simple
    let () = elpi_stuff := ((!elpi_stuff) @ [elpi_simple])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
open Elpi.API
[@@@warning "-26-27-32-39-60"]
let rec test : type h c.
  depth:int ->
    h ->
      c ->
        State.t ->
          RawData.term -> (State.t * simple * Conversion.extra_goals)
  = elpi_readback_simple
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
