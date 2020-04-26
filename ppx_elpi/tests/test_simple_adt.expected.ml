let elpi_stuff = ref []
let pp_simple _ _ = ()
type simple =
  | A 
  | B of int [@@deriving elpi { append = elpi_stuff }]
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
    let rec elpi_embed_simple :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (simple, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.embedding
      =
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
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (simple, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.readback
      =
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
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"simple";
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"a" ~doc:"A"
                 ~args:[];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"b" ~doc:"B"
                 ~args:[(Elpi.API.ContextualConversion.(!>)
                           Elpi.API.BuiltInData.int).Elpi.API.ContextualConversion.ty]);
        pp = pp_simple;
        embed = elpi_embed_simple;
        readback = elpi_readback_simple
      }
    let elpi_simple = Elpi.API.BuiltIn.MLDataC simple
    let () =
      elpi_stuff :=
        ((!elpi_stuff) @
           ([elpi_simple] @
              [Elpi.API.BuiltIn.LPCode
                 (String.concat "\n"
                    ["pred map.simple  i:simple, o:simple.";
                    "map.simple a a.";
                    Printf.sprintf "map.%s %s(%s %s) (%s %s) :- %s." "simple"
                      "" "b" "A0" "b" "B0"
                      (String.concat ", "
                         ["(" ^
                            ("(=)" ^ (" " ^ ("A0" ^ (" " ^ ("B0" ^ ")")))))]);
                    "\n"])]))
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
open Elpi.API
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
