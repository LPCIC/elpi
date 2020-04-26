let elpi_stuff = ref []
let pp_simple _ _ = ()
type simple[@@elpi.opaque
             {
               Elpi.API.OpaqueData.name = "simple";
               doc = "";
               pp = (fun fmt -> fun _ -> Format.fprintf fmt "<simple>");
               compare = Pervasives.compare;
               hash = Hashtbl.hash;
               hconsed = false;
               constants = []
             }][@@deriving elpi { declaration = elpi_stuff }]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_simple = "simple"
    let elpi_constant_type_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_simple
    let elpi_opaque_data_decl_simple =
      Elpi.API.RawOpaqueData.declare
        {
          Elpi.API.OpaqueData.name = "simple";
          doc = "";
          pp = (fun fmt -> fun _ -> Format.fprintf fmt "<simple>");
          compare = Pervasives.compare;
          hash = Hashtbl.hash;
          hconsed = false;
          constants = []
        }
    module Ctx_for_simple =
      struct class type t = object inherit Elpi.API.Conversion.ctx end end
    let simple :
      'c . (simple, #Elpi.API.Conversion.ctx as 'c) Elpi.API.Conversion.t =
      let name = "simple" in
      let ({ Elpi.API.RawOpaqueData.cin = cin; isc; cout; name = c },
           constants_map, doc)
        = elpi_opaque_data_decl_simple in
      let ty = Elpi.API.Conversion.TyName name in
      let embed ~depth:_  _ _ state x =
        (state, (Elpi.API.RawData.mkCData (cin x)), []) in
      let readback ~depth  _ _ state t =
        match Elpi.API.RawData.look ~depth t with
        | Elpi.API.RawData.CData c when isc c -> (state, (cout c), [])
        | Elpi.API.RawData.Const i when i < 0 ->
            (try
               (state,
                 (snd @@
                    (Elpi.API.RawData.Constants.Map.find i constants_map)),
                 [])
             with
             | Not_found ->
                 raise (Elpi.API.Conversion.TypeErr (ty, depth, t)))
        | _ -> raise (Elpi.API.Conversion.TypeErr (ty, depth, t)) in
      let pp_doc fmt () =
        if doc <> ""
        then
          (Elpi.API.PPX.Doc.comment fmt ("% " ^ doc);
           Format.fprintf fmt "@\n");
        Format.fprintf fmt "@[<hov 2>typeabbrev %s (ctype \"%s\").@]@\n@\n"
          name c;
        Elpi.API.RawData.Constants.Map.iter
          (fun _ ->
             fun (c, _) ->
               Format.fprintf fmt "@[<hov 2>type %s %s.@]@\n" c name)
          constants_map in
      {
        Elpi.API.Conversion.embed = embed;
        readback;
        ty;
        pp_doc;
        pp = (fun fmt -> fun x -> Elpi.API.RawOpaqueData.pp fmt (cin x))
      }
    let elpi_embed_simple = simple.Elpi.API.Conversion.embed
    let elpi_readback_simple = simple.Elpi.API.Conversion.readback
    let elpi_simple = Elpi.API.BuiltIn.MLData simple
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
let test : 'h . (simple, #Conversion.ctx as 'h) Conversion.t = simple
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
