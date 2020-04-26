let elpi_stuff = ref []
let pp_simple _ _ = ()
type simple =
  | A 
  | B of int [@@deriving elpi { declaration = elpi_stuff }]
include
  struct
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_simple = "simple"
    let elpi_constant_type_simplec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_simple
    let elpi_constant_constructor_simple_A = "a"
    let elpi_constant_constructor_simple_Ac =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_simple_A
    let elpi_constant_constructor_simple_B = "b"
    let elpi_constant_constructor_simple_Bc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_simple_B
    module Ctx_for_simple =
      struct class type t = object inherit Elpi.API.Conversion.ctx end end
    let rec elpi_embed_simple :
      'c . (simple, #Ctx_for_simple.t as 'c) Elpi.API.Conversion.embedding =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | A ->
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_simple_Ac []),
                    (List.concat []))
              | B elpi__3 ->
                  let (elpi__state, elpi__5, elpi__4) =
                    Elpi.API.PPX.embed_int ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__3 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_simple_Bc [elpi__5]),
                    (List.concat [elpi__4]))
    let rec elpi_readback_simple :
      'c . (simple, #Ctx_for_simple.t as 'c) Elpi.API.Conversion.readback =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.Const elpi__hd when
                    elpi__hd == elpi_constant_constructor_simple_Ac ->
                    (elpi__state, A, [])
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_simple_Bc ->
                    let (elpi__state, elpi__2, elpi__1) =
                      Elpi.API.PPX.readback_int ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | [] ->
                         (elpi__state, (B elpi__2), (List.concat [elpi__1]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_simple_Bc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "simple" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    let simple : 'c . (simple, #Ctx_for_simple.t as 'c) Elpi.API.Conversion.t
      =
      let kind = Elpi.API.Conversion.TyName "simple" in
      {
        Elpi.API.Conversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"simple";
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"a" ~doc:"A"
                 ~args:[];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"b" ~doc:"B"
                 ~args:[Elpi.API.BuiltInData.int.Elpi.API.Conversion.ty]);
        pp = pp_simple;
        embed = elpi_embed_simple;
        readback = elpi_readback_simple
      }
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
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
