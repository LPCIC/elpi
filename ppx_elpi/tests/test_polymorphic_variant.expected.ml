let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type shape =
  [ `Dot  | `Circle of int  | `Rect of (int * int) 
  | `Hidden of bool [@elpi.code "secret"]][@@deriving
                                            (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let pp_shape :
      Ppx_deriving_runtime.Format.formatter ->
        shape -> Ppx_deriving_runtime.unit
      =
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | `Dot -> Ppx_deriving_runtime.Format.pp_print_string fmt "`Dot"
            | `Circle x ->
                (Ppx_deriving_runtime.Format.fprintf fmt "`Circle (@[<hov>";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") x;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | `Rect x ->
                (Ppx_deriving_runtime.Format.fprintf fmt "`Rect (@[<hov>";
                 ((fun (a0, a1) ->
                     Ppx_deriving_runtime.Format.fprintf fmt "(@[";
                     ((Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                      Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                      (Ppx_deriving_runtime.Format.fprintf fmt "%d") a1);
                     Ppx_deriving_runtime.Format.fprintf fmt "@])")) x;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | `Hidden x ->
                (Ppx_deriving_runtime.Format.fprintf fmt "`Hidden (@[<hov>";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%B") x;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])"))
      [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_shape : shape -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_shape x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_shape = "shape"
    let elpi_constant_type_shapec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_shape
    let elpi_constant_constructor_shape_Dot = "dot"
    let elpi_constant_constructor_shape_Dotc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_shape_Dot
    let elpi_constant_constructor_shape_Circle = "circle"
    let elpi_constant_constructor_shape_Circlec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_shape_Circle
    let elpi_constant_constructor_shape_Rect = "rect"
    let elpi_constant_constructor_shape_Rectc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_shape_Rect
    let elpi_constant_constructor_shape_Hidden = "secret"
    let elpi_constant_constructor_shape_Hiddenc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_shape_Hidden
    module Ctx_for_shape =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_shape :
      'c 'csts . (shape, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | `Dot ->
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_shape_Dotc []), (List.concat []))
        | `Circle elpi__9 ->
            let (elpi__state, elpi__11, elpi__10) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__9 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_shape_Circlec [elpi__11]),
              (List.concat [elpi__10]))
        | `Rect (elpi__12, elpi__13) ->
            let (elpi__state, elpi__16, elpi__14) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__12 in
            let (elpi__state, elpi__17, elpi__15) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__13 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_shape_Rectc [elpi__16; elpi__17]),
              (List.concat [elpi__14; elpi__15]))
        | `Hidden elpi__18 ->
            let (elpi__state, elpi__20, elpi__19) =
              (fun ~depth h c s t ->
                 Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__18 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_shape_Hiddenc [elpi__20]),
              (List.concat [elpi__19]))
    and elpi_readback_shape :
      'c 'csts . (shape, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.Const elpi__hd when
            elpi__hd == elpi_constant_constructor_shape_Dotc ->
            (elpi__state, `Dot, [])
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_shape_Circlec ->
            let (elpi__state, elpi__2, elpi__1) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | [] ->
                 (elpi__state, (`Circle elpi__2), (List.concat [elpi__1]))
             | _ ->
                 Elpi.API.Error.error ~component:"ppx_elpi"
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_shape_Circlec)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_shape_Rectc ->
            let (elpi__state, elpi__6, elpi__5) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | elpi__3::[] ->
                 let (elpi__state, elpi__3, elpi__4) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__3 in
                 (elpi__state, (`Rect (elpi__6, elpi__3)),
                   (List.concat [elpi__5; elpi__4]))
             | _ ->
                 Elpi.API.Error.error ~component:"ppx_elpi"
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_shape_Rectc)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_shape_Hiddenc ->
            let (elpi__state, elpi__8, elpi__7) =
              (fun ~depth h c s t ->
                 Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | [] ->
                 (elpi__state, (`Hidden elpi__8), (List.concat [elpi__7]))
             | _ ->
                 Elpi.API.Error.error ~component:"ppx_elpi"
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_shape_Hiddenc)))
        | _ ->
            Elpi.API.Error.error ~component:"ppx_elpi"
              (Format.asprintf "Not a constructor of type %s: %a" "shape"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and shape : 'c 'csts . (shape, 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "shape" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:6 ~variant:""
               ~ty:kind ~name:"dot" ~doc:"Dot" ~args:[];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:6 ~variant:""
               ~ty:kind ~name:"circle" ~doc:"Circle"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:6 ~variant:""
               ~ty:kind ~name:"rect" ~doc:"Rect"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:6 ~variant:""
               ~ty:kind ~name:"secret" ~doc:"Hidden"
               ~args:[Elpi.Builtin.PPX.bool.Elpi.API.ContextualConversion.ty]);
        constants =
          [elpi_constant_constructor_shape_Dotc;
          elpi_constant_constructor_shape_Circlec;
          elpi_constant_constructor_shape_Rectc;
          elpi_constant_constructor_shape_Hiddenc];
        pp = pp_shape;
        embed = elpi_embed_shape;
        readback = elpi_readback_shape
      }
    let elpi_shape = Elpi.API.BuiltIn.MLDataC shape
    let elpi__shape__deep_copy =
      "func shape.copy shape -> shape.\nshape.copy dot dot.\nshape.copy (circle A0) (circle B0) :- (int.copy A0 B0).\nshape.copy (rect A0 A1) (rect B0 B1) :- (int.copy A0 B0), (int.copy A1 B1).\nshape.copy (secret A0) (secret B0) :- (bool.copy A0 B0).\n\n"
    class ctx_for_shape (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_shape.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_shape :
      (Ctx_for_shape.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s -> (s, ((new ctx_for_shape) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_shape; Elpi.API.BuiltIn.LPCode elpi__shape__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type 'a tagged = [ `Plain  | `Tag of 'a ][@@deriving
                                           (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let pp_tagged :
      'a .
        (Ppx_deriving_runtime.Format.formatter ->
           'a -> Ppx_deriving_runtime.unit)
          ->
          Ppx_deriving_runtime.Format.formatter ->
            'a tagged -> Ppx_deriving_runtime.unit
      =
      ((let open! Ppx_deriving_runtime in
          fun poly_a fmt ->
            function
            | `Plain ->
                Ppx_deriving_runtime.Format.pp_print_string fmt "`Plain"
            | `Tag x ->
                (Ppx_deriving_runtime.Format.fprintf fmt "`Tag (@[<hov>";
                 (poly_a fmt) x;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])"))
      [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_tagged :
      'a .
        (Ppx_deriving_runtime.Format.formatter ->
           'a -> Ppx_deriving_runtime.unit)
          -> 'a tagged -> Ppx_deriving_runtime.string
      =
      fun poly_a x ->
        Ppx_deriving_runtime.Format.asprintf "%a" (pp_tagged poly_a) x
      [@@ocaml.warning "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_tagged = "tagged"
    let elpi_constant_type_taggedc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_tagged
    let elpi_constant_constructor_tagged_Plain = "plain"
    let elpi_constant_constructor_tagged_Plainc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tagged_Plain
    let elpi_constant_constructor_tagged_Tag = "tag"
    let elpi_constant_constructor_tagged_Tagc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tagged_Tag
    module Ctx_for_tagged =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_tagged :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.embedding
          ->
          ('elpi__param__a tagged, 'c, 'csts)
            Elpi.API.ContextualConversion.embedding
      =
      fun elpi_embed_elpi__param__a ~depth:elpi__depth elpi__hyps
        elpi__constraints elpi__state elpi__fun_arg ->
        match elpi__fun_arg with
        | `Plain ->
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_tagged_Plainc []),
              (List.concat []))
        | `Tag elpi__23 ->
            let (elpi__state, elpi__25, elpi__24) =
              (fun ~depth h c s t -> elpi_embed_elpi__param__a ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__23 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_tagged_Tagc [elpi__25]),
              (List.concat [elpi__24]))
    and elpi_readback_tagged :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.readback
          ->
          ('elpi__param__a tagged, 'c, 'csts)
            Elpi.API.ContextualConversion.readback
      =
      fun elpi_readback_elpi__param__a ~depth:elpi__depth elpi__hyps
        elpi__constraints elpi__state elpi__x ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.Const elpi__hd when
            elpi__hd == elpi_constant_constructor_tagged_Plainc ->
            (elpi__state, `Plain, [])
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_tagged_Tagc ->
            let (elpi__state, elpi__22, elpi__21) =
              (fun ~depth h c s t ->
                 elpi_readback_elpi__param__a ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | [] -> (elpi__state, (`Tag elpi__22), (List.concat [elpi__21]))
             | _ ->
                 Elpi.API.Error.error ~component:"ppx_elpi"
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_tagged_Tagc)))
        | _ ->
            Elpi.API.Error.error ~component:"ppx_elpi"
              (Format.asprintf "Not a constructor of type %s: %a" "tagged"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and tagged :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, 'c, 'csts) Elpi.API.ContextualConversion.t ->
          ('elpi__param__a tagged, 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      fun elpi__param__a ->
        let kind =
          Elpi.API.ContextualConversion.TyApp
            ("tagged", (elpi__param__a.Elpi.API.ContextualConversion.ty), []) in
        {
          Elpi.API.ContextualConversion.ty = kind;
          pp_doc =
            (fun fmt () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:""
                 ~ty:kind ~name:"plain" ~doc:"Plain" ~args:[];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:""
                 ~ty:kind ~name:"tag" ~doc:"Tag"
                 ~args:[elpi__param__a.Elpi.API.ContextualConversion.ty]);
          constants =
            [elpi_constant_constructor_tagged_Plainc;
            elpi_constant_constructor_tagged_Tagc];
          pp = (pp_tagged elpi__param__a.pp);
          embed =
            (elpi_embed_tagged
               elpi__param__a.Elpi.API.ContextualConversion.embed);
          readback =
            (elpi_readback_tagged
               elpi__param__a.Elpi.API.ContextualConversion.readback)
        }
    let elpi_tagged =
      Elpi.API.BuiltIn.MLDataC (tagged (Elpi.API.BuiltInData.polyC "A"))
    let elpi__tagged__deep_copy =
      "func tagged.copy (func X0 -> Y0), tagged X0 -> tagged Y0.\ntagged.copy _ plain plain.\ntagged.copy F0 (tag A0) (tag B0) :- (F0 A0 B0).\n\n"
    class ctx_for_tagged (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tagged.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_tagged :
      (Ctx_for_tagged.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s ->
        (s, ((new ctx_for_tagged) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_tagged; Elpi.API.BuiltIn.LPCode elpi__tagged__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
open BuiltInPredicate.Notation
let grow =
  BuiltInPredicate.ContextualPred
    ("grow",
      (fun ~depth:_ hyps constraints state ->
         (state, ((new PPX.ctx) hyps), constraints, [])),
      (In (shape, "S", (Out (shape, "T", (Read "T is S, twice as large"))))),
      (fun (s : shape) (_ : shape BuiltInPredicate.oarg) ~depth:_ _ _ _ ->
         !:
           (match s with
            | `Dot -> `Dot
            | `Circle r -> `Circle (2 * r)
            | `Rect (w, h) -> `Rect ((2 * w), (2 * h))
            | `Hidden b -> `Hidden (not b))))
let builtin =
  BuiltIn.declare ~file_name
    ((PPX.to_list declaration) @ [BuiltIn.MLCode (grow, BuiltIn.DocAbove)])
let program =
  {|
main :-
  shape.copy (rect 1 2) X, X = rect 1 2,
  grow dot dot,
  grow (circle 3) (circle 6),
  grow (rect 1 2) (rect 2 4),
  grow (secret tt) (secret ff),
  tagged.copy shape.copy (tag (circle 1)) Y, Y = tag (circle 1),
  tagged.copy shape.copy plain Z, Z = plain.
|}
let () = Ppx_tests_lib.run_program builtin program
