let elpi_stuff = ref []
let pp_simple _ _ _ = ()
type 'a simple =
  | A 
  | B of int 
  | C of 'a * int [@@deriving elpi { declaration = elpi_stuff }]
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
    let elpi_constant_constructor_simple_C = "c"
    let elpi_constant_constructor_simple_Cc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_simple_C
    module Ctx_for_simple =
      struct class type t = object inherit Elpi.API.Conversion.ctx end end
    let rec elpi_embed_simple :
      'elpi__param__a 'c .
        ('elpi__param__a, 'c) Elpi.API.Conversion.embedding ->
          ('elpi__param__a simple, #Ctx_for_simple.t as 'c)
            Elpi.API.Conversion.embedding
      =
      fun elpi_embed_elpi__param__a ->
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
                | B elpi__7 ->
                    let (elpi__state, elpi__9, elpi__8) =
                      Elpi.API.PPX.embed_int ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__7 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppL
                         elpi_constant_constructor_simple_Bc [elpi__9]),
                      (List.concat [elpi__8]))
                | C (elpi__10, elpi__11) ->
                    let (elpi__state, elpi__14, elpi__12) =
                      elpi_embed_elpi__param__a ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__10 in
                    let (elpi__state, elpi__15, elpi__13) =
                      Elpi.API.PPX.embed_int ~depth:elpi__depth elpi__hyps
                        elpi__constraints elpi__state elpi__11 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppL
                         elpi_constant_constructor_simple_Cc
                         [elpi__14; elpi__15]),
                      (List.concat [elpi__12; elpi__13]))
    let rec elpi_readback_simple :
      'elpi__param__a 'c .
        ('elpi__param__a, 'c) Elpi.API.Conversion.readback ->
          ('elpi__param__a simple, #Ctx_for_simple.t as 'c)
            Elpi.API.Conversion.readback
      =
      fun elpi_readback_elpi__param__a ->
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
                        Elpi.API.PPX.readback_int ~depth:elpi__depth
                          elpi__hyps elpi__constraints elpi__state elpi__x in
                      (match elpi__xs with
                       | [] ->
                           (elpi__state, (B elpi__2),
                             (List.concat [elpi__1]))
                       | _ ->
                           Elpi.API.Utils.type_error
                             ("Not enough arguments to constructor: " ^
                                (Elpi.API.RawData.Constants.show
                                   elpi_constant_constructor_simple_Bc)))
                  | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                      elpi__hd == elpi_constant_constructor_simple_Cc ->
                      let (elpi__state, elpi__6, elpi__5) =
                        elpi_readback_elpi__param__a ~depth:elpi__depth
                          elpi__hyps elpi__constraints elpi__state elpi__x in
                      (match elpi__xs with
                       | elpi__3::[] ->
                           let (elpi__state, elpi__3, elpi__4) =
                             Elpi.API.PPX.readback_int ~depth:elpi__depth
                               elpi__hyps elpi__constraints elpi__state
                               elpi__3 in
                           (elpi__state, (C (elpi__6, elpi__3)),
                             (List.concat [elpi__5; elpi__4]))
                       | _ ->
                           Elpi.API.Utils.type_error
                             ("Not enough arguments to constructor: " ^
                                (Elpi.API.RawData.Constants.show
                                   elpi_constant_constructor_simple_Cc)))
                  | _ ->
                      Elpi.API.Utils.type_error
                        (Format.asprintf "Not a constructor of type %s: %a"
                           "simple" (Elpi.API.RawPp.term elpi__depth) elpi__x)
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
               fun () ->
                 Elpi.API.PPX.Doc.kind fmt kind ~doc:"simple";
                 (Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"a"
                    ~doc:"A" ~args:[];
                  Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"b"
                    ~doc:"B"
                    ~args:[Elpi.API.BuiltInData.int.Elpi.API.Conversion.ty]);
                 Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"c" ~doc:"C"
                   ~args:[elpi__param__a.Elpi.API.Conversion.ty;
                         Elpi.API.BuiltInData.int.Elpi.API.Conversion.ty]);
          pp = (pp_simple elpi__param__a.pp);
          embed =
            (elpi_embed_simple elpi__param__a.Elpi.API.Conversion.embed);
          readback =
            (elpi_readback_simple elpi__param__a.Elpi.API.Conversion.readback)
        }
    let elpi_simple =
      Elpi.API.BuiltIn.MLData (simple (Elpi.API.BuiltInData.poly "A0"))
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
class type o =
  object inherit Elpi.API.Conversion.ctx method  foobar : bool end
let (_ : (int simple, o) Elpi.API.Conversion.t) =
  simple Elpi.API.BuiltInData.int
let (_ : (float simple, o) Elpi.API.Conversion.t) =
  simple Elpi.API.BuiltInData.float
open Elpi.API
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!elpi_stuff)
let main () =
  let (_elpi, _) = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin; exit 0
;;main ()
