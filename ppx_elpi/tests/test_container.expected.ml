let declaration = ref []
let pp_loc _ _ _ = ()
type 'a loc = {
  loc: int ;
  data: 'a }[@@deriving elpi { declaration }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_loc = "loc"
    let elpi_constant_type_locc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_loc
    let elpi_constant_constructor_loc_loc = "loc"
    let elpi_constant_constructor_loc_locc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_loc_loc
    module Ctx_for_loc =
      struct
        class type t = object inherit Elpi.API.ContextualConversion.ctx end
      end
    let rec elpi_embed_loc :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, #Ctx_for_loc.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding ->
          ('elpi__param__a loc, #Ctx_for_loc.t as 'c, 'csts)
            Elpi.API.ContextualConversion.embedding
      =
      fun elpi_embed_elpi__param__a ->
        fun ~depth:elpi__depth ->
          fun elpi__hyps ->
            fun elpi__constraints ->
              fun elpi__state ->
                function
                | { loc = elpi__5; data = elpi__6 } ->
                    let (elpi__state, elpi__9, elpi__7) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.embed
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__5 in
                    let (elpi__state, elpi__10, elpi__8) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 elpi_embed_elpi__param__a ~depth h c s t)
                        ~depth:elpi__depth elpi__hyps elpi__constraints
                        elpi__state elpi__6 in
                    (elpi__state,
                      (Elpi.API.RawData.mkAppL
                         elpi_constant_constructor_loc_locc
                         [elpi__9; elpi__10]),
                      (List.concat [elpi__7; elpi__8]))
    and elpi_readback_loc :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, #Ctx_for_loc.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback ->
          ('elpi__param__a loc, #Ctx_for_loc.t as 'c, 'csts)
            Elpi.API.ContextualConversion.readback
      =
      fun elpi_readback_elpi__param__a ->
        fun ~depth:elpi__depth ->
          fun elpi__hyps ->
            fun elpi__constraints ->
              fun elpi__state ->
                fun elpi__x ->
                  match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                  | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                      elpi__hd == elpi_constant_constructor_loc_locc ->
                      let (elpi__state, elpi__4, elpi__3) =
                        (fun ~depth ->
                           fun h ->
                             fun c ->
                               fun s ->
                                 fun t ->
                                   Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.readback
                                     ~depth h c s t) ~depth:elpi__depth
                          elpi__hyps elpi__constraints elpi__state elpi__x in
                      (match elpi__xs with
                       | elpi__1::[] ->
                           let (elpi__state, elpi__1, elpi__2) =
                             (fun ~depth ->
                                fun h ->
                                  fun c ->
                                    fun s ->
                                      fun t ->
                                        elpi_readback_elpi__param__a ~depth h
                                          c s t) ~depth:elpi__depth
                               elpi__hyps elpi__constraints elpi__state
                               elpi__1 in
                           (elpi__state, { loc = elpi__4; data = elpi__1 },
                             (List.concat [elpi__3; elpi__2]))
                       | _ ->
                           Elpi.API.Utils.type_error
                             ("Not enough arguments to constructor: " ^
                                (Elpi.API.RawData.Constants.show
                                   elpi_constant_constructor_loc_locc)))
                  | _ ->
                      Elpi.API.Utils.type_error
                        (Format.asprintf "Not a constructor of type %s: %a"
                           "loc" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and loc :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, #Ctx_for_loc.t as 'c, 'csts)
          Elpi.API.ContextualConversion.t ->
          ('elpi__param__a loc, #Ctx_for_loc.t as 'c, 'csts)
            Elpi.API.ContextualConversion.t
      =
      fun elpi__param__a ->
        let kind =
          Elpi.API.ContextualConversion.TyApp
            ("loc", (elpi__param__a.Elpi.API.ContextualConversion.ty), []) in
        {
          Elpi.API.ContextualConversion.ty = kind;
          pp_doc =
            (fun fmt ->
               fun () ->
                 Elpi.API.PPX.Doc.kind fmt kind ~doc:"loc";
                 Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"loc"
                   ~doc:"loc"
                   ~args:[Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.ty;
                         elpi__param__a.Elpi.API.ContextualConversion.ty]);
          pp = (pp_loc elpi__param__a.pp);
          embed =
            (elpi_embed_loc
               elpi__param__a.Elpi.API.ContextualConversion.embed);
          readback =
            (elpi_readback_loc
               elpi__param__a.Elpi.API.ContextualConversion.readback)
        }
    let elpi_loc =
      Elpi.API.BuiltIn.MLDataC (loc Elpi.API.BuiltInContextualData.polyA0)
    class ctx_for_loc (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_loc.t =
      object (_) inherit  ((Elpi.API.ContextualConversion.ctx) h) end
    let (in_ctx_for_loc :
      (Ctx_for_loc.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_loc) h s), c, (List.concat []))
    let () = declaration := ((!declaration) @ [elpi_loc])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let pp_term _ _ = ()
type term =
  | A of int 
  | B of string * bool [@@deriving elpi { declaration }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_term = "term"
    let elpi_constant_type_termc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_term
    let elpi_constant_constructor_term_A = "a"
    let elpi_constant_constructor_term_Ac =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_A
    let elpi_constant_constructor_term_B = "b"
    let elpi_constant_constructor_term_Bc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_B
    module Ctx_for_term =
      struct
        class type t = object inherit Elpi.API.ContextualConversion.ctx end
      end
    let rec elpi_embed_term :
      'c 'csts .
        (term, #Ctx_for_term.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              function
              | A elpi__17 ->
                  let (elpi__state, elpi__19, elpi__18) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.embed
                                 ~depth h c s t) ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__17 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_term_Ac [elpi__19]),
                    (List.concat [elpi__18]))
              | B (elpi__20, elpi__21) ->
                  let (elpi__state, elpi__24, elpi__22) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.embed
                                 ~depth h c s t) ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__20 in
                  let (elpi__state, elpi__25, elpi__23) =
                    (fun ~depth ->
                       fun h ->
                         fun c ->
                           fun s ->
                             fun t ->
                               Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed
                                 ~depth h c s t) ~depth:elpi__depth
                      elpi__hyps elpi__constraints elpi__state elpi__21 in
                  (elpi__state,
                    (Elpi.API.RawData.mkAppL
                       elpi_constant_constructor_term_Bc [elpi__24; elpi__25]),
                    (List.concat [elpi__22; elpi__23]))
    and elpi_readback_term :
      'c 'csts .
        (term, #Ctx_for_term.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth ->
        fun elpi__hyps ->
          fun elpi__constraints ->
            fun elpi__state ->
              fun elpi__x ->
                match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Ac ->
                    let (elpi__state, elpi__12, elpi__11) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | [] ->
                         (elpi__state, (A elpi__12),
                           (List.concat [elpi__11]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Ac)))
                | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                    elpi__hd == elpi_constant_constructor_term_Bc ->
                    let (elpi__state, elpi__16, elpi__15) =
                      (fun ~depth ->
                         fun h ->
                           fun c ->
                             fun s ->
                               fun t ->
                                 Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.readback
                                   ~depth h c s t) ~depth:elpi__depth
                        elpi__hyps elpi__constraints elpi__state elpi__x in
                    (match elpi__xs with
                     | elpi__13::[] ->
                         let (elpi__state, elpi__13, elpi__14) =
                           (fun ~depth ->
                              fun h ->
                                fun c ->
                                  fun s ->
                                    fun t ->
                                      Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback
                                        ~depth h c s t) ~depth:elpi__depth
                             elpi__hyps elpi__constraints elpi__state
                             elpi__13 in
                         (elpi__state, (B (elpi__16, elpi__13)),
                           (List.concat [elpi__15; elpi__14]))
                     | _ ->
                         Elpi.API.Utils.type_error
                           ("Not enough arguments to constructor: " ^
                              (Elpi.API.RawData.Constants.show
                                 elpi_constant_constructor_term_Bc)))
                | _ ->
                    Elpi.API.Utils.type_error
                      (Format.asprintf "Not a constructor of type %s: %a"
                         "term" (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and term :
      'c 'csts .
        (term, #Ctx_for_term.t as 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "term" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt ->
             fun () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"term";
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"a" ~doc:"A"
                 ~args:[Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.ty];
               Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"b" ~doc:"B"
                 ~args:[Elpi.API.BuiltInContextualData.string.Elpi.API.ContextualConversion.ty;
                       Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty]);
        pp = pp_term;
        embed = elpi_embed_term;
        readback = elpi_readback_term
      }
    let elpi_term = Elpi.API.BuiltIn.MLDataC term
    class ctx_for_term (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_term.t =
      object (_) inherit  ((Elpi.API.ContextualConversion.ctx) h) end
    let (in_ctx_for_term :
      (Ctx_for_term.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s -> (s, ((new ctx_for_term) h s), c, (List.concat []))
    let () = declaration := ((!declaration) @ [elpi_term])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let pp_x _ _ = ()
type x = (term loc * int)[@@deriving elpi { declaration }]
include
  struct
    [@@@ocaml.warning "-60"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_x = "x"
    let elpi_constant_type_xc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_x
    module Ctx_for_x =
      struct
        class type t = object inherit Elpi.API.ContextualConversion.ctx end
      end
    let rec elpi_embed_x :
      'c 'csts .
        (x, #Ctx_for_x.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                (Elpi.Builtin.PPX.embed_pair
                   (loc term).Elpi.API.ContextualConversion.embed
                   Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.embed)
                  ~depth h c s t
    and elpi_readback_x :
      'c 'csts .
        (x, #Ctx_for_x.t as 'c, 'csts) Elpi.API.ContextualConversion.readback
      =
      fun ~depth ->
        fun h ->
          fun c ->
            fun s ->
              fun t ->
                (Elpi.Builtin.PPX.readback_pair
                   (loc term).Elpi.API.ContextualConversion.readback
                   Elpi.API.BuiltInContextualData.int.Elpi.API.ContextualConversion.readback)
                  ~depth h c s t
    and x :
      'c 'csts .
        (x, #Ctx_for_x.t as 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "x" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt -> fun () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:"x"; ());
        pp = pp_x;
        embed = elpi_embed_x;
        readback = elpi_readback_x
      }
    let elpi_x =
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           ("x" ^
              (" " ^
                 (((let open Elpi.API.PPX.Doc in show_ty_ast ~prec:AppArg) @@
                     (Elpi.Builtin.PPX.pair (loc term)
                        Elpi.API.BuiltInContextualData.int).Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "x")))))
    class ctx_for_x (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_x.t =
      object (_) inherit  ((Elpi.API.ContextualConversion.ctx) h) end
    let (in_ctx_for_x :
      (Ctx_for_x.t, 'csts) Elpi.API.ContextualConversion.ctx_readback) =
      fun ~depth ->
        fun h ->
          fun c -> fun s -> (s, ((new ctx_for_x) h s), c, (List.concat []))
    let () = declaration := ((!declaration) @ [elpi_x])
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let xx : 'c 'csts . (x, 'c, 'csts) Elpi.API.ContextualConversion.t = x
open Elpi.API
let builtin =
  let open BuiltIn in declare ~file_name:(Sys.argv.(1)) (!declaration)
let main () =
  let _elpi = Setup.init ~builtins:[builtin] () in
  BuiltIn.document_file builtin; exit 0
;;main ()
