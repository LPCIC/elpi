let elpi_stuff = ref []
let pp_simple _ _ = ()
let pp_mut _ _ = ()
type simple =
  | A 
  | B of int * mut 
and mut =
  | C 
  | D of simple [@@deriving elpi { append = elpi_stuff }]
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
    let elpi_constant_type_mut = "mut"
    let elpi_constant_type_mutc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_mut
    let elpi_constant_constructor_mut_C = "c"
    let elpi_constant_constructor_mut_Cc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_mut_C
    let elpi_constant_constructor_mut_D = "d"
    let elpi_constant_constructor_mut_Dc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_mut_D
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
              | B (elpi__5, elpi__6) ->
                  let (elpi__state, elpi__9, elpi__7) =
                    Elpi.API.PPX.embed_int ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__5 in
                  let (elpi__state, elpi__10, elpi__8) =
                    elpi_embed_mut ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__6 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_simple_Bc
                       [elpi__9; elpi__10]),
                    (List.concat [elpi__7; elpi__8]))
    and elpi_embed_mut :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (mut, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | C ->
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL elpi_constant_constructor_mut_Cc
                       []), (List.concat []))
              | D elpi__13 ->
                  let (elpi__state, elpi__15, elpi__14) =
                    elpi_embed_simple ~depth:elpi__depth elpi__hyps
                      elpi__constraints elpi__state elpi__13 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL elpi_constant_constructor_mut_Dc
                       [elpi__15]), (List.concat [elpi__14]))
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
                    let (elpi__state, elpi__4, elpi__3) =
                      Elpi.API.PPX.readback_int ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__1::[] ->
                         let (elpi__state, elpi__1, elpi__2) =
                           elpi_readback_mut ~depth:elpi__depth elpi__hyps
                             elpi__constraints elpi__state elpi__1 in
                         (elpi__state, (B (elpi__4, elpi__1)),
                           (List.concat [elpi__3; elpi__2]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_simple_Bc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "simple" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and elpi_readback_mut :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (mut, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.Const elpi__hd when
                    elpi__hd == elpi_constant_constructor_mut_Cc ->
                    (elpi__state, C, [])
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_mut_Dc ->
                    let (elpi__state, elpi__12, elpi__11) =
                      elpi_readback_simple ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | [] ->
                         (elpi__state, (D elpi__12),
                           (List.concat [elpi__11]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_mut_Dc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "mut" (Elpi.API.RawPp.term elpi__depth) elpi__x)
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
                           Elpi.API.BuiltInData.int).Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyName
                         elpi_constant_type_mut]);
        pp = pp_simple;
        embed = elpi_embed_simple;
        readback = elpi_readback_simple
      }
    let mut :
      'elpi__param__poly_hyps 'elpi__param__poly_csts .
        (mut, 'elpi__param__poly_hyps, 'elpi__param__poly_csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "mut" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"mut";
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"c" ~doc:"C"
                 ~args:[];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"d" ~doc:"D"
                 ~args:[Elpi.API.ContextualConversion.TyName
                          elpi_constant_type_simple]);
        pp = pp_mut;
        embed = elpi_embed_mut;
        readback = elpi_readback_mut
      }
    let elpi_simple = Elpi.API.BuiltIn.MLDataC simple
    let elpi_mut = Elpi.API.BuiltIn.MLDataC mut
    let () =
      elpi_stuff :=
        ((!elpi_stuff) @
           ([elpi_simple; elpi_mut] @
              [Elpi.API.BuiltIn.LPCode
                 (String.concat "\n"
                    ["pred map.simple  i:simple, o:simple.";
                    "map.simple a a.";
                    Printf.sprintf "map.%s %s(%s %s) (%s %s) :- %s." "simple"
                      "" "b" "A0 A1" "b" "B0 B1"
                      (String.concat ", "
                         ["(" ^
                            ("(=)" ^ (" " ^ ("A0" ^ (" " ^ ("B0" ^ ")")))));
                         "(" ^
                           (("map." ^ elpi_constant_type_mut) ^
                              (" " ^ ("A1" ^ (" " ^ ("B1" ^ ")")))))]);
                    "\n"]);
              Elpi.API.BuiltIn.LPCode
                (String.concat "\n"
                   ["pred map.mut  i:mut, o:mut.";
                   "map.mut c c.";
                   Printf.sprintf "map.%s %s(%s %s) (%s %s) :- %s." "mut" ""
                     "d" "A0" "d" "B0"
                     (String.concat ", "
                        ["(" ^
                           (("map." ^ elpi_constant_type_simple) ^
                              (" " ^ ("A0" ^ (" " ^ ("B0" ^ ")")))))]);
                   "\n"])]))
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
open Elpi.API
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
