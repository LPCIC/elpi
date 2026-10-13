let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show = Format.asprintf "%a" pp
  end
type c1 =
  | E1 of ((string)[@elpi.key "t1"]) * int [@@elpi.index (module String)]
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let pp_c1 :
      Ppx_deriving_runtime.Format.formatter ->
        c1 -> Ppx_deriving_runtime.unit
      =
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | E1 (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.E1 (@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%d") a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
      [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_c1 : c1 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_c1 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_c1 = "c1"
    let elpi_constant_type_c1c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_c1
    let elpi_constant_constructor_c1_E1 = "e1"
    let elpi_constant_constructor_c1_E1c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_c1_E1
    module Elpi_c1_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_c1_state =
      Elpi.API.State.declare_component ~name:"c1"
        ~pp:(fun fmt _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_c1_Map.empty : Elpi.API.RawData.constant
                                         Elpi_c1_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : c1
                                                             Elpi.API.PPX.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x) ()
    let elpi_c1_to_key ~depth:_ elpi__fun_arg =
      match elpi__fun_arg with | E1 (elpi__16, _) -> elpi__16
    let elpi_is_c1 { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x } =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_c1_E1c)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Utils.type_error
                   "context entry applied to a non bound variable")
          else None
      | _ -> None
    let elpi_push_c1 ~depth:elpi__depth elpi__state elpi__name elpi__ctx_item
      =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_c1_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_c1_Map.add elpi__name elpi__i elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item
          elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_c1_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    let elpi_pop_c1 ~depth:elpi__depth elpi__state elpi__name =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_c1_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_c1_Map.remove elpi__name elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_c1_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    module Ctx_for_c1 =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_c1 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c1), 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | (elpi__9, E1 (elpi__7, elpi__8)) ->
            let (elpi__state, elpi__13, elpi__10) =
              (fun ~depth elpi__hyps elpi__constraints elpi__state elpi__i ->
                 if elpi__i < 0
                 then Elpi.API.Utils.type_error "not a bound variable";
                 (elpi__state, (Elpi.API.RawData.mkConst elpi__i), []))
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__9 in
            let (elpi__state, elpi__14, elpi__11) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__7 in
            let (elpi__state, elpi__15, elpi__12) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__8 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_c1_E1c
                 [elpi__13; elpi__14; elpi__15]),
              (List.concat [elpi__10; elpi__11; elpi__12]))
    and elpi_readback_c1 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c1), 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_c1_E1c ->
            let (elpi__state, elpi__6, elpi__5) =
              (fun ~depth elpi__hyps elpi__constraints elpi__state elpi__t ->
                 match Elpi.API.RawData.look ~depth elpi__t with
                 | Elpi.API.RawData.Const elpi__i when elpi__i >= 0 ->
                     (elpi__state, elpi__i, [])
                 | _ -> Elpi.API.Utils.type_error "not a bound variable")
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | elpi__1::elpi__2::[] ->
                 let (elpi__state, elpi__1, elpi__3) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__1 in
                 let (elpi__state, elpi__2, elpi__4) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__2 in
                 (elpi__state, (elpi__6, (E1 (elpi__1, elpi__2))),
                   (List.concat [elpi__5; elpi__3; elpi__4]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_c1_E1c)))
        | _ ->
            Elpi.API.Utils.type_error
              (Format.asprintf "Not a constructor of type %s: %a" "c1"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and c1 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c1), 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "c1" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             ();
             Elpi.API.PPX.Doc.context_entry fmt ~name:"e1" ~doc:"E1"
               ~key:(Elpi.API.ContextualConversion.TyName "t1")
               ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt (_, x) -> pp_c1 fmt x);
        embed = elpi_embed_c1;
        readback = elpi_readback_c1
      }
    let context_made_of_c1 =
      {
        Elpi.API.PPX.is_entry_for_bound_var = elpi_is_c1;
        to_key = elpi_c1_to_key;
        push = elpi_push_c1;
        pop = elpi_pop_c1;
        conv = c1;
        init =
          (fun state ->
             Elpi.API.State.set elpi_c1_state state
               ((Elpi_c1_Map.empty : Elpi.API.RawData.constant Elpi_c1_Map.t),
                 (Elpi.API.RawData.Constants.Map.empty : c1
                                                           Elpi.API.PPX.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get = (fun state -> snd @@ (Elpi.API.State.get elpi_c1_state state))
      }
    let elpi_c1 = Elpi.API.BuiltIn.MLDataC c1
    class ctx_for_c1 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_c1.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_c1 :
      (Ctx_for_c1.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s -> (s, ((new ctx_for_c1) h s), c, (List.concat []))
    let () = Elpi.API.PPX.add_declarations declaration [elpi_c1]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type t1 =
  | V1 of string [@elpi.var c1]
  | A1 of t1 * t1 
  | K1 of int [@elpi.code "k"][@elpi.variant 1]
  | L1 of int * string * ((t1)[@elpi.binder "t1" c1 (fun i s -> E1 (s, i))]) 
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_t1 :
      Ppx_deriving_runtime.Format.formatter ->
        t1 -> Ppx_deriving_runtime.unit
      =
      let __2 = pp_t1
      and __1 = pp_t1
      and __0 = pp_t1 in
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | V1 a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.V1@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | A1 (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.A1 (@,";
                 ((__0 fmt) a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__1 fmt) a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
            | K1 a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.K1@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | L1 (a0, a1, a2) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.L1 (@,";
                 (((Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__2 fmt) a2);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
        [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_t1 : t1 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_t1 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_t1 = "t1"
    let elpi_constant_type_t1c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_t1
    let elpi_constant_constructor_t1_V1 = "v1"
    let elpi_constant_constructor_t1_V1c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t1_V1
    let elpi_constant_constructor_t1_A1 = "a1"
    let elpi_constant_constructor_t1_A1c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t1_A1
    let elpi_constant_constructor_t1_K1 = "k"
    let elpi_constant_constructor_t1_K1c =
      Elpi.API.RawData.Constants.declare_global_symbol ~variant:1
        elpi_constant_constructor_t1_K1
    let elpi_constant_constructor_t1_L1 = "l1"
    let elpi_constant_constructor_t1_L1c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t1_L1
    module Ctx_for_t1 =
      struct
        class type t =
          object
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_c1.t
            method  c1 : c1 Elpi.API.PPX.ctx_field
          end
      end
    let rec elpi_embed_t1 :
      'c 'csts .
        (t1, #Ctx_for_t1.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | V1 elpi__31 ->
            let (elpi__ctx2dbl, _) =
              Elpi.API.State.get elpi_c1_state elpi__state in
            let elpi__key = (fun x -> x) elpi__31 in
            (if not (Elpi_c1_Map.mem elpi__key elpi__ctx2dbl)
             then Elpi.API.Utils.error "Unbound variable";
             (elpi__state,
               (Elpi.API.RawData.mkBound
                  (Elpi_c1_Map.find elpi__key elpi__ctx2dbl)), []))
        | A1 (elpi__34, elpi__35) ->
            let (elpi__state, elpi__38, elpi__36) =
              (fun ~depth h c s t -> elpi_embed_t1 ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__34 in
            let (elpi__state, elpi__39, elpi__37) =
              (fun ~depth h c s t -> elpi_embed_t1 ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__35 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_t1_A1c
                 [elpi__38; elpi__39]), (List.concat [elpi__36; elpi__37]))
        | K1 elpi__40 ->
            let (elpi__state, elpi__42, elpi__41) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__40 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_t1_K1c
                 [elpi__42]), (List.concat [elpi__41]))
        | L1 (elpi__43, elpi__44, elpi__45) ->
            let (elpi__state, elpi__49, elpi__46) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__43 in
            let (elpi__state, elpi__50, elpi__47) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__44 in
            let elpi__ctx_entry = (fun i s -> E1 (s, i)) elpi__43 elpi__44 in
            let elpi__ctx_key =
              elpi_c1_to_key ~depth:elpi__depth elpi__ctx_entry in
            let elpi__ctx_entry =
              { Elpi.API.PPX.entry = elpi__ctx_entry; depth = elpi__depth } in
            let elpi__state =
              elpi_push_c1 ~depth:elpi__depth elpi__state elpi__ctx_key
                elpi__ctx_entry in
            let (elpi__state, elpi__52, elpi__48) =
              (fun ~depth h c s t -> elpi_embed_t1 ~depth h c s t)
                ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                elpi__state elpi__45 in
            let elpi__51 = Elpi.API.RawData.mkLam elpi__52 in
            let elpi__state =
              elpi_pop_c1 ~depth:elpi__depth elpi__state elpi__ctx_key in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_t1_L1c
                 [elpi__49; elpi__50; elpi__51]),
              (List.concat [elpi__46; elpi__47; elpi__48]))
    and elpi_readback_t1 :
      'c 'csts .
        (t1, #Ctx_for_t1.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.Const elpi__hd when elpi__hd >= 0 ->
            let (_, elpi__dbl2ctx) =
              Elpi.API.State.get elpi_c1_state elpi__state in
            (if
               not
                 (Elpi.API.RawData.Constants.Map.mem elpi__hd elpi__dbl2ctx)
             then
               Elpi.API.Utils.error
                 (Format.asprintf "Unbound variable: %s in %a"
                    (Elpi.API.RawData.Constants.show elpi__hd)
                    (Elpi.API.RawData.Constants.Map.pp
                       (Elpi.API.PPX.pp_ctx_entry pp_c1)) elpi__dbl2ctx);
             (let { Elpi.API.PPX.entry = elpi__entry; depth = elpi__depth } =
                Elpi.API.RawData.Constants.Map.find elpi__hd elpi__dbl2ctx in
              (elpi__state,
                (V1 (elpi_c1_to_key ~depth:elpi__depth elpi__entry)), [])))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_t1_A1c ->
            let (elpi__state, elpi__22, elpi__21) =
              (fun ~depth h c s t -> elpi_readback_t1 ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | elpi__19::[] ->
                 let (elpi__state, elpi__19, elpi__20) =
                   (fun ~depth h c s t -> elpi_readback_t1 ~depth h c s t)
                     ~depth:elpi__depth elpi__hyps elpi__constraints
                     elpi__state elpi__19 in
                 (elpi__state, (A1 (elpi__22, elpi__19)),
                   (List.concat [elpi__21; elpi__20]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_t1_A1c)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_t1_K1c ->
            let (elpi__state, elpi__24, elpi__23) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | [] -> (elpi__state, (K1 elpi__24), (List.concat [elpi__23]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_t1_K1c)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_t1_L1c ->
            let (elpi__state, elpi__30, elpi__29) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | elpi__25::elpi__26::[] ->
                 let (elpi__state, elpi__25, elpi__27) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__25 in
                 let elpi__ctx_entry =
                   (fun i s -> E1 (s, i)) elpi__30 elpi__25 in
                 let elpi__ctx_key =
                   elpi_c1_to_key ~depth:elpi__depth elpi__ctx_entry in
                 let elpi__ctx_entry =
                   {
                     Elpi.API.PPX.entry = elpi__ctx_entry;
                     depth = elpi__depth
                   } in
                 let elpi__state =
                   elpi_push_c1 ~depth:elpi__depth elpi__state elpi__ctx_key
                     elpi__ctx_entry in
                 let (elpi__state, elpi__26, elpi__28) =
                   match Elpi.API.RawData.look ~depth:elpi__depth elpi__26
                   with
                   | Elpi.API.RawData.Lam elpi__bo ->
                       ((fun ~depth h c s t ->
                           elpi_readback_t1 ~depth h c s t))
                         ~depth:(elpi__depth + 1) elpi__hyps
                         elpi__constraints elpi__state elpi__bo
                   | _ -> assert false in
                 let elpi__state =
                   elpi_pop_c1 ~depth:elpi__depth elpi__state elpi__ctx_key in
                 (elpi__state, (L1 (elpi__30, elpi__25, elpi__26)),
                   (List.concat [elpi__29; elpi__27; elpi__28]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_t1_L1c)))
        | _ ->
            Elpi.API.Utils.type_error
              (Format.asprintf "Not a constructor of type %s: %a" "t1"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and t1 :
      'c 'csts .
        (t1, #Ctx_for_t1.t as 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "t1" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
               ~ty:kind ~name:"a1" ~doc:"A1"
               ~args:[Elpi.API.ContextualConversion.TyName
                        elpi_constant_type_t1;
                     Elpi.API.ContextualConversion.TyName
                       elpi_constant_type_t1];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:1
               ~ty:kind ~name:"k" ~doc:"K1"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
               ~ty:kind ~name:"l1" ~doc:"L1"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.ContextualConversion.TyApp
                       ("->", (Elpi.API.ContextualConversion.TyName "t1"),
                         [Elpi.API.ContextualConversion.TyName
                            elpi_constant_type_t1])]);
        pp = pp_t1;
        embed = elpi_embed_t1;
        readback = elpi_readback_t1
      }
    let elpi_t1 = Elpi.API.BuiltIn.MLDataC t1
    let elpi__t1__deep_copy =
      "func t1.copy t1 -> t1.\nt1.copy (a1 A0 A1) (a1 B0 B1) :- (t1.copy A0 B0), (t1.copy A1 B1).\nt1.copy (k A0) (k B0) :- (int.copy A0 B0).\nt1.copy (l1 A0 A1 A2) (l1 B0 B1 B2) :- (int.copy A0 B0), (string.copy A1 B1), (pi x\\ e1 x B1 B0 ==> t1.copy x x ==> (t1.copy (A2 x) (B2 x))).\n\n"
    class ctx_for_t1 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_t1.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_c1) h s)
        method c1 = context_made_of_c1.Elpi.API.PPX.get s
      end
    let in_ctx_for_t1 :
      (Ctx_for_t1.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s ->
        let ctx = (new ctx_for_c1) h s in
        let (s, gls0) =
          Elpi.API.PPX.readback_context ~depth context_made_of_c1 ctx h c s in
        (s, ((new ctx_for_t1) h s), c, (List.concat [gls0]))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_t1; Elpi.API.BuiltIn.LPCode elpi__t1__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let t1 : 'c 'csts . (t1, #ctx_for_t1 as 'c, 'csts) ContextualConversion.t =
  t1
type c2 =
  | E2 of ((string)[@elpi.key "t2"]) * int [@@elpi.index (module String)]
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let pp_c2 :
      Ppx_deriving_runtime.Format.formatter ->
        c2 -> Ppx_deriving_runtime.unit
      =
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | E2 (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.E2 (@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%d") a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
      [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_c2 : c2 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_c2 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_c2 = "c2"
    let elpi_constant_type_c2c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_c2
    let elpi_constant_constructor_c2_E2 = "e2"
    let elpi_constant_constructor_c2_E2c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_c2_E2
    module Elpi_c2_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_c2_state =
      Elpi.API.State.declare_component ~name:"c2"
        ~pp:(fun fmt _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_c2_Map.empty : Elpi.API.RawData.constant
                                         Elpi_c2_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : c2
                                                             Elpi.API.PPX.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x) ()
    let elpi_c2_to_key ~depth:_ elpi__fun_arg =
      match elpi__fun_arg with | E2 (elpi__68, _) -> elpi__68
    let elpi_is_c2 { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x } =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_c2_E2c)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Utils.type_error
                   "context entry applied to a non bound variable")
          else None
      | _ -> None
    let elpi_push_c2 ~depth:elpi__depth elpi__state elpi__name elpi__ctx_item
      =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_c2_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_c2_Map.add elpi__name elpi__i elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item
          elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_c2_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    let elpi_pop_c2 ~depth:elpi__depth elpi__state elpi__name =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_c2_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_c2_Map.remove elpi__name elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_c2_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    module Ctx_for_c2 =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_c2 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c2), 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | (elpi__61, E2 (elpi__59, elpi__60)) ->
            let (elpi__state, elpi__65, elpi__62) =
              (fun ~depth elpi__hyps elpi__constraints elpi__state elpi__i ->
                 if elpi__i < 0
                 then Elpi.API.Utils.type_error "not a bound variable";
                 (elpi__state, (Elpi.API.RawData.mkConst elpi__i), []))
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__61 in
            let (elpi__state, elpi__66, elpi__63) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__59 in
            let (elpi__state, elpi__67, elpi__64) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__60 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_c2_E2c
                 [elpi__65; elpi__66; elpi__67]),
              (List.concat [elpi__62; elpi__63; elpi__64]))
    and elpi_readback_c2 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c2), 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_c2_E2c ->
            let (elpi__state, elpi__58, elpi__57) =
              (fun ~depth elpi__hyps elpi__constraints elpi__state elpi__t ->
                 match Elpi.API.RawData.look ~depth elpi__t with
                 | Elpi.API.RawData.Const elpi__i when elpi__i >= 0 ->
                     (elpi__state, elpi__i, [])
                 | _ -> Elpi.API.Utils.type_error "not a bound variable")
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | elpi__53::elpi__54::[] ->
                 let (elpi__state, elpi__53, elpi__55) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__53 in
                 let (elpi__state, elpi__54, elpi__56) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__54 in
                 (elpi__state, (elpi__58, (E2 (elpi__53, elpi__54))),
                   (List.concat [elpi__57; elpi__55; elpi__56]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_c2_E2c)))
        | _ ->
            Elpi.API.Utils.type_error
              (Format.asprintf "Not a constructor of type %s: %a" "c2"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and c2 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c2), 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "c2" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             ();
             Elpi.API.PPX.Doc.context_entry fmt ~name:"e2" ~doc:"E2"
               ~key:(Elpi.API.ContextualConversion.TyName "t2")
               ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt (_, x) -> pp_c2 fmt x);
        embed = elpi_embed_c2;
        readback = elpi_readback_c2
      }
    let context_made_of_c2 =
      {
        Elpi.API.PPX.is_entry_for_bound_var = elpi_is_c2;
        to_key = elpi_c2_to_key;
        push = elpi_push_c2;
        pop = elpi_pop_c2;
        conv = c2;
        init =
          (fun state ->
             Elpi.API.State.set elpi_c2_state state
               ((Elpi_c2_Map.empty : Elpi.API.RawData.constant Elpi_c2_Map.t),
                 (Elpi.API.RawData.Constants.Map.empty : c2
                                                           Elpi.API.PPX.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get = (fun state -> snd @@ (Elpi.API.State.get elpi_c2_state state))
      }
    let elpi_c2 = Elpi.API.BuiltIn.MLDataC c2
    class ctx_for_c2 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_c2.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_c2 :
      (Ctx_for_c2.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s -> (s, ((new ctx_for_c2) h s), c, (List.concat []))
    let () = Elpi.API.PPX.add_declarations declaration [elpi_c2]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type t2 =
  | V2 of string [@elpi.var c2]
  | A2 of t2 * t2 
  | K2 of int [@elpi.code "k"][@elpi.variant 2]
  | L2 of int * string * ((t2)[@elpi.binder "t2" c2 (fun i s -> E2 (s, i))]) 
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_t2 :
      Ppx_deriving_runtime.Format.formatter ->
        t2 -> Ppx_deriving_runtime.unit
      =
      let __2 = pp_t2
      and __1 = pp_t2
      and __0 = pp_t2 in
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | V2 a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.V2@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | A2 (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.A2 (@,";
                 ((__0 fmt) a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__1 fmt) a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
            | K2 a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.K2@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | L2 (a0, a1, a2) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.L2 (@,";
                 (((Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__2 fmt) a2);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
        [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_t2 : t2 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_t2 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_t2 = "t2"
    let elpi_constant_type_t2c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_t2
    let elpi_constant_constructor_t2_V2 = "v2"
    let elpi_constant_constructor_t2_V2c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t2_V2
    let elpi_constant_constructor_t2_A2 = "a2"
    let elpi_constant_constructor_t2_A2c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t2_A2
    let elpi_constant_constructor_t2_K2 = "k"
    let elpi_constant_constructor_t2_K2c =
      Elpi.API.RawData.Constants.declare_global_symbol ~variant:2
        elpi_constant_constructor_t2_K2
    let elpi_constant_constructor_t2_L2 = "l2"
    let elpi_constant_constructor_t2_L2c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t2_L2
    module Ctx_for_t2 =
      struct
        class type t =
          object
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_c2.t
            method  c2 : c2 Elpi.API.PPX.ctx_field
          end
      end
    let rec elpi_embed_t2 :
      'c 'csts .
        (t2, #Ctx_for_t2.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | V2 elpi__83 ->
            let (elpi__ctx2dbl, _) =
              Elpi.API.State.get elpi_c2_state elpi__state in
            let elpi__key = (fun x -> x) elpi__83 in
            (if not (Elpi_c2_Map.mem elpi__key elpi__ctx2dbl)
             then Elpi.API.Utils.error "Unbound variable";
             (elpi__state,
               (Elpi.API.RawData.mkBound
                  (Elpi_c2_Map.find elpi__key elpi__ctx2dbl)), []))
        | A2 (elpi__86, elpi__87) ->
            let (elpi__state, elpi__90, elpi__88) =
              (fun ~depth h c s t -> elpi_embed_t2 ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__86 in
            let (elpi__state, elpi__91, elpi__89) =
              (fun ~depth h c s t -> elpi_embed_t2 ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__87 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_t2_A2c
                 [elpi__90; elpi__91]), (List.concat [elpi__88; elpi__89]))
        | K2 elpi__92 ->
            let (elpi__state, elpi__94, elpi__93) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__92 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_t2_K2c
                 [elpi__94]), (List.concat [elpi__93]))
        | L2 (elpi__95, elpi__96, elpi__97) ->
            let (elpi__state, elpi__101, elpi__98) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__95 in
            let (elpi__state, elpi__102, elpi__99) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__96 in
            let elpi__ctx_entry = (fun i s -> E2 (s, i)) elpi__95 elpi__96 in
            let elpi__ctx_key =
              elpi_c2_to_key ~depth:elpi__depth elpi__ctx_entry in
            let elpi__ctx_entry =
              { Elpi.API.PPX.entry = elpi__ctx_entry; depth = elpi__depth } in
            let elpi__state =
              elpi_push_c2 ~depth:elpi__depth elpi__state elpi__ctx_key
                elpi__ctx_entry in
            let (elpi__state, elpi__104, elpi__100) =
              (fun ~depth h c s t -> elpi_embed_t2 ~depth h c s t)
                ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                elpi__state elpi__97 in
            let elpi__103 = Elpi.API.RawData.mkLam elpi__104 in
            let elpi__state =
              elpi_pop_c2 ~depth:elpi__depth elpi__state elpi__ctx_key in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_t2_L2c
                 [elpi__101; elpi__102; elpi__103]),
              (List.concat [elpi__98; elpi__99; elpi__100]))
    and elpi_readback_t2 :
      'c 'csts .
        (t2, #Ctx_for_t2.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.Const elpi__hd when elpi__hd >= 0 ->
            let (_, elpi__dbl2ctx) =
              Elpi.API.State.get elpi_c2_state elpi__state in
            (if
               not
                 (Elpi.API.RawData.Constants.Map.mem elpi__hd elpi__dbl2ctx)
             then
               Elpi.API.Utils.error
                 (Format.asprintf "Unbound variable: %s in %a"
                    (Elpi.API.RawData.Constants.show elpi__hd)
                    (Elpi.API.RawData.Constants.Map.pp
                       (Elpi.API.PPX.pp_ctx_entry pp_c2)) elpi__dbl2ctx);
             (let { Elpi.API.PPX.entry = elpi__entry; depth = elpi__depth } =
                Elpi.API.RawData.Constants.Map.find elpi__hd elpi__dbl2ctx in
              (elpi__state,
                (V2 (elpi_c2_to_key ~depth:elpi__depth elpi__entry)), [])))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_t2_A2c ->
            let (elpi__state, elpi__74, elpi__73) =
              (fun ~depth h c s t -> elpi_readback_t2 ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | elpi__71::[] ->
                 let (elpi__state, elpi__71, elpi__72) =
                   (fun ~depth h c s t -> elpi_readback_t2 ~depth h c s t)
                     ~depth:elpi__depth elpi__hyps elpi__constraints
                     elpi__state elpi__71 in
                 (elpi__state, (A2 (elpi__74, elpi__71)),
                   (List.concat [elpi__73; elpi__72]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_t2_A2c)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_t2_K2c ->
            let (elpi__state, elpi__76, elpi__75) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | [] -> (elpi__state, (K2 elpi__76), (List.concat [elpi__75]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_t2_K2c)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_t2_L2c ->
            let (elpi__state, elpi__82, elpi__81) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | elpi__77::elpi__78::[] ->
                 let (elpi__state, elpi__77, elpi__79) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__77 in
                 let elpi__ctx_entry =
                   (fun i s -> E2 (s, i)) elpi__82 elpi__77 in
                 let elpi__ctx_key =
                   elpi_c2_to_key ~depth:elpi__depth elpi__ctx_entry in
                 let elpi__ctx_entry =
                   {
                     Elpi.API.PPX.entry = elpi__ctx_entry;
                     depth = elpi__depth
                   } in
                 let elpi__state =
                   elpi_push_c2 ~depth:elpi__depth elpi__state elpi__ctx_key
                     elpi__ctx_entry in
                 let (elpi__state, elpi__78, elpi__80) =
                   match Elpi.API.RawData.look ~depth:elpi__depth elpi__78
                   with
                   | Elpi.API.RawData.Lam elpi__bo ->
                       ((fun ~depth h c s t ->
                           elpi_readback_t2 ~depth h c s t))
                         ~depth:(elpi__depth + 1) elpi__hyps
                         elpi__constraints elpi__state elpi__bo
                   | _ -> assert false in
                 let elpi__state =
                   elpi_pop_c2 ~depth:elpi__depth elpi__state elpi__ctx_key in
                 (elpi__state, (L2 (elpi__82, elpi__77, elpi__78)),
                   (List.concat [elpi__81; elpi__79; elpi__80]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_t2_L2c)))
        | _ ->
            Elpi.API.Utils.type_error
              (Format.asprintf "Not a constructor of type %s: %a" "t2"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and t2 :
      'c 'csts .
        (t2, #Ctx_for_t2.t as 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "t2" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
               ~ty:kind ~name:"a2" ~doc:"A2"
               ~args:[Elpi.API.ContextualConversion.TyName
                        elpi_constant_type_t2;
                     Elpi.API.ContextualConversion.TyName
                       elpi_constant_type_t2];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:2
               ~ty:kind ~name:"k" ~doc:"K2"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
               ~ty:kind ~name:"l2" ~doc:"L2"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.ContextualConversion.TyApp
                       ("->", (Elpi.API.ContextualConversion.TyName "t2"),
                         [Elpi.API.ContextualConversion.TyName
                            elpi_constant_type_t2])]);
        pp = pp_t2;
        embed = elpi_embed_t2;
        readback = elpi_readback_t2
      }
    let elpi_t2 = Elpi.API.BuiltIn.MLDataC t2
    let elpi__t2__deep_copy =
      "func t2.copy t2 -> t2.\nt2.copy (a2 A0 A1) (a2 B0 B1) :- (t2.copy A0 B0), (t2.copy A1 B1).\nt2.copy (k A0) (k B0) :- (int.copy A0 B0).\nt2.copy (l2 A0 A1 A2) (l2 B0 B1 B2) :- (int.copy A0 B0), (string.copy A1 B1), (pi x\\ e2 x B1 B0 ==> t2.copy x x ==> (t2.copy (A2 x) (B2 x))).\n\n"
    class ctx_for_t2 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_t2.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_c2) h s)
        method c2 = context_made_of_c2.Elpi.API.PPX.get s
      end
    let in_ctx_for_t2 :
      (Ctx_for_t2.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s ->
        let ctx = (new ctx_for_c2) h s in
        let (s, gls0) =
          Elpi.API.PPX.readback_context ~depth context_made_of_c2 ctx h c s in
        (s, ((new ctx_for_t2) h s), c, (List.concat [gls0]))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_t2; Elpi.API.BuiltIn.LPCode elpi__t2__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let t2 : 'c 'csts . (t2, #ctx_for_t2 as 'c, 'csts) ContextualConversion.t =
  t2
type c3 =
  | E3 of ((string)[@elpi.key "t3"]) * int [@@elpi.index (module String)]
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let pp_c3 :
      Ppx_deriving_runtime.Format.formatter ->
        c3 -> Ppx_deriving_runtime.unit
      =
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | E3 (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.E3 (@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%d") a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
      [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_c3 : c3 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_c3 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_c3 = "c3"
    let elpi_constant_type_c3c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_c3
    let elpi_constant_constructor_c3_E3 = "e3"
    let elpi_constant_constructor_c3_E3c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_c3_E3
    module Elpi_c3_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_c3_state =
      Elpi.API.State.declare_component ~name:"c3"
        ~pp:(fun fmt _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_c3_Map.empty : Elpi.API.RawData.constant
                                         Elpi_c3_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : c3
                                                             Elpi.API.PPX.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x) ()
    let elpi_c3_to_key ~depth:_ elpi__fun_arg =
      match elpi__fun_arg with | E3 (elpi__120, _) -> elpi__120
    let elpi_is_c3 { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x } =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_c3_E3c)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Utils.type_error
                   "context entry applied to a non bound variable")
          else None
      | _ -> None
    let elpi_push_c3 ~depth:elpi__depth elpi__state elpi__name elpi__ctx_item
      =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_c3_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_c3_Map.add elpi__name elpi__i elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item
          elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_c3_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    let elpi_pop_c3 ~depth:elpi__depth elpi__state elpi__name =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_c3_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_c3_Map.remove elpi__name elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_c3_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    module Ctx_for_c3 =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_c3 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c3), 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | (elpi__113, E3 (elpi__111, elpi__112)) ->
            let (elpi__state, elpi__117, elpi__114) =
              (fun ~depth elpi__hyps elpi__constraints elpi__state elpi__i ->
                 if elpi__i < 0
                 then Elpi.API.Utils.type_error "not a bound variable";
                 (elpi__state, (Elpi.API.RawData.mkConst elpi__i), []))
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__113 in
            let (elpi__state, elpi__118, elpi__115) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__111 in
            let (elpi__state, elpi__119, elpi__116) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__112 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_c3_E3c
                 [elpi__117; elpi__118; elpi__119]),
              (List.concat [elpi__114; elpi__115; elpi__116]))
    and elpi_readback_c3 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c3), 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_c3_E3c ->
            let (elpi__state, elpi__110, elpi__109) =
              (fun ~depth elpi__hyps elpi__constraints elpi__state elpi__t ->
                 match Elpi.API.RawData.look ~depth elpi__t with
                 | Elpi.API.RawData.Const elpi__i when elpi__i >= 0 ->
                     (elpi__state, elpi__i, [])
                 | _ -> Elpi.API.Utils.type_error "not a bound variable")
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | elpi__105::elpi__106::[] ->
                 let (elpi__state, elpi__105, elpi__107) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__105 in
                 let (elpi__state, elpi__106, elpi__108) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__106 in
                 (elpi__state, (elpi__110, (E3 (elpi__105, elpi__106))),
                   (List.concat [elpi__109; elpi__107; elpi__108]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_c3_E3c)))
        | _ ->
            Elpi.API.Utils.type_error
              (Format.asprintf "Not a constructor of type %s: %a" "c3"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and c3 :
      'c 'csts .
        ((Elpi.API.RawData.constant * c3), 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "c3" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             ();
             Elpi.API.PPX.Doc.context_entry fmt ~name:"e3" ~doc:"E3"
               ~key:(Elpi.API.ContextualConversion.TyName "t3")
               ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt (_, x) -> pp_c3 fmt x);
        embed = elpi_embed_c3;
        readback = elpi_readback_c3
      }
    let context_made_of_c3 =
      {
        Elpi.API.PPX.is_entry_for_bound_var = elpi_is_c3;
        to_key = elpi_c3_to_key;
        push = elpi_push_c3;
        pop = elpi_pop_c3;
        conv = c3;
        init =
          (fun state ->
             Elpi.API.State.set elpi_c3_state state
               ((Elpi_c3_Map.empty : Elpi.API.RawData.constant Elpi_c3_Map.t),
                 (Elpi.API.RawData.Constants.Map.empty : c3
                                                           Elpi.API.PPX.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get = (fun state -> snd @@ (Elpi.API.State.get elpi_c3_state state))
      }
    let elpi_c3 = Elpi.API.BuiltIn.MLDataC c3
    class ctx_for_c3 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_c3.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_c3 :
      (Ctx_for_c3.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s -> (s, ((new ctx_for_c3) h s), c, (List.concat []))
    let () = Elpi.API.PPX.add_declarations declaration [elpi_c3]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type t3 =
  | V3 of string [@elpi.var c3]
  | A3 of t3 * t3 
  | K3 of int [@elpi.code "k"][@elpi.variant 3]
  | L3 of int * string * ((t3)[@elpi.binder "t3" c3 (fun i s -> E3 (s, i))]) 
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_t3 :
      Ppx_deriving_runtime.Format.formatter ->
        t3 -> Ppx_deriving_runtime.unit
      =
      let __2 = pp_t3
      and __1 = pp_t3
      and __0 = pp_t3 in
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | V3 a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.V3@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | A3 (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.A3 (@,";
                 ((__0 fmt) a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__1 fmt) a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
            | K3 a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.K3@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | L3 (a0, a1, a2) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_three_contexts.L3 (@,";
                 (((Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                   Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%S") a1);
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__2 fmt) a2);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
        [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_t3 : t3 -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_t3 x[@@ocaml.warning
                                                                  "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_t3 = "t3"
    let elpi_constant_type_t3c =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_t3
    let elpi_constant_constructor_t3_V3 = "v3"
    let elpi_constant_constructor_t3_V3c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t3_V3
    let elpi_constant_constructor_t3_A3 = "a3"
    let elpi_constant_constructor_t3_A3c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t3_A3
    let elpi_constant_constructor_t3_K3 = "k"
    let elpi_constant_constructor_t3_K3c =
      Elpi.API.RawData.Constants.declare_global_symbol ~variant:3
        elpi_constant_constructor_t3_K3
    let elpi_constant_constructor_t3_L3 = "l3"
    let elpi_constant_constructor_t3_L3c =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_t3_L3
    module Ctx_for_t3 =
      struct
        class type t =
          object
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_c3.t
            method  c3 : c3 Elpi.API.PPX.ctx_field
          end
      end
    let rec elpi_embed_t3 :
      'c 'csts .
        (t3, #Ctx_for_t3.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | V3 elpi__135 ->
            let (elpi__ctx2dbl, _) =
              Elpi.API.State.get elpi_c3_state elpi__state in
            let elpi__key = (fun x -> x) elpi__135 in
            (if not (Elpi_c3_Map.mem elpi__key elpi__ctx2dbl)
             then Elpi.API.Utils.error "Unbound variable";
             (elpi__state,
               (Elpi.API.RawData.mkBound
                  (Elpi_c3_Map.find elpi__key elpi__ctx2dbl)), []))
        | A3 (elpi__138, elpi__139) ->
            let (elpi__state, elpi__142, elpi__140) =
              (fun ~depth h c s t -> elpi_embed_t3 ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__138 in
            let (elpi__state, elpi__143, elpi__141) =
              (fun ~depth h c s t -> elpi_embed_t3 ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__139 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_t3_A3c
                 [elpi__142; elpi__143]),
              (List.concat [elpi__140; elpi__141]))
        | K3 elpi__144 ->
            let (elpi__state, elpi__146, elpi__145) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__144 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_t3_K3c
                 [elpi__146]), (List.concat [elpi__145]))
        | L3 (elpi__147, elpi__148, elpi__149) ->
            let (elpi__state, elpi__153, elpi__150) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__147 in
            let (elpi__state, elpi__154, elpi__151) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__148 in
            let elpi__ctx_entry = (fun i s -> E3 (s, i)) elpi__147 elpi__148 in
            let elpi__ctx_key =
              elpi_c3_to_key ~depth:elpi__depth elpi__ctx_entry in
            let elpi__ctx_entry =
              { Elpi.API.PPX.entry = elpi__ctx_entry; depth = elpi__depth } in
            let elpi__state =
              elpi_push_c3 ~depth:elpi__depth elpi__state elpi__ctx_key
                elpi__ctx_entry in
            let (elpi__state, elpi__156, elpi__152) =
              (fun ~depth h c s t -> elpi_embed_t3 ~depth h c s t)
                ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                elpi__state elpi__149 in
            let elpi__155 = Elpi.API.RawData.mkLam elpi__156 in
            let elpi__state =
              elpi_pop_c3 ~depth:elpi__depth elpi__state elpi__ctx_key in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL elpi_constant_constructor_t3_L3c
                 [elpi__153; elpi__154; elpi__155]),
              (List.concat [elpi__150; elpi__151; elpi__152]))
    and elpi_readback_t3 :
      'c 'csts .
        (t3, #Ctx_for_t3.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.Const elpi__hd when elpi__hd >= 0 ->
            let (_, elpi__dbl2ctx) =
              Elpi.API.State.get elpi_c3_state elpi__state in
            (if
               not
                 (Elpi.API.RawData.Constants.Map.mem elpi__hd elpi__dbl2ctx)
             then
               Elpi.API.Utils.error
                 (Format.asprintf "Unbound variable: %s in %a"
                    (Elpi.API.RawData.Constants.show elpi__hd)
                    (Elpi.API.RawData.Constants.Map.pp
                       (Elpi.API.PPX.pp_ctx_entry pp_c3)) elpi__dbl2ctx);
             (let { Elpi.API.PPX.entry = elpi__entry; depth = elpi__depth } =
                Elpi.API.RawData.Constants.Map.find elpi__hd elpi__dbl2ctx in
              (elpi__state,
                (V3 (elpi_c3_to_key ~depth:elpi__depth elpi__entry)), [])))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_t3_A3c ->
            let (elpi__state, elpi__126, elpi__125) =
              (fun ~depth h c s t -> elpi_readback_t3 ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | elpi__123::[] ->
                 let (elpi__state, elpi__123, elpi__124) =
                   (fun ~depth h c s t -> elpi_readback_t3 ~depth h c s t)
                     ~depth:elpi__depth elpi__hyps elpi__constraints
                     elpi__state elpi__123 in
                 (elpi__state, (A3 (elpi__126, elpi__123)),
                   (List.concat [elpi__125; elpi__124]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_t3_A3c)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_t3_K3c ->
            let (elpi__state, elpi__128, elpi__127) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | [] -> (elpi__state, (K3 elpi__128), (List.concat [elpi__127]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_t3_K3c)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_t3_L3c ->
            let (elpi__state, elpi__134, elpi__133) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | elpi__129::elpi__130::[] ->
                 let (elpi__state, elpi__129, elpi__131) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__129 in
                 let elpi__ctx_entry =
                   (fun i s -> E3 (s, i)) elpi__134 elpi__129 in
                 let elpi__ctx_key =
                   elpi_c3_to_key ~depth:elpi__depth elpi__ctx_entry in
                 let elpi__ctx_entry =
                   {
                     Elpi.API.PPX.entry = elpi__ctx_entry;
                     depth = elpi__depth
                   } in
                 let elpi__state =
                   elpi_push_c3 ~depth:elpi__depth elpi__state elpi__ctx_key
                     elpi__ctx_entry in
                 let (elpi__state, elpi__130, elpi__132) =
                   match Elpi.API.RawData.look ~depth:elpi__depth elpi__130
                   with
                   | Elpi.API.RawData.Lam elpi__bo ->
                       ((fun ~depth h c s t ->
                           elpi_readback_t3 ~depth h c s t))
                         ~depth:(elpi__depth + 1) elpi__hyps
                         elpi__constraints elpi__state elpi__bo
                   | _ -> assert false in
                 let elpi__state =
                   elpi_pop_c3 ~depth:elpi__depth elpi__state elpi__ctx_key in
                 (elpi__state, (L3 (elpi__134, elpi__129, elpi__130)),
                   (List.concat [elpi__133; elpi__131; elpi__132]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_t3_L3c)))
        | _ ->
            Elpi.API.Utils.type_error
              (Format.asprintf "Not a constructor of type %s: %a" "t3"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and t3 :
      'c 'csts .
        (t3, #Ctx_for_t3.t as 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "t3" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
               ~ty:kind ~name:"a3" ~doc:"A3"
               ~args:[Elpi.API.ContextualConversion.TyName
                        elpi_constant_type_t3;
                     Elpi.API.ContextualConversion.TyName
                       elpi_constant_type_t3];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:3
               ~ty:kind ~name:"k" ~doc:"K3"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:2 ~variant:0
               ~ty:kind ~name:"l3" ~doc:"L3"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.ContextualConversion.TyApp
                       ("->", (Elpi.API.ContextualConversion.TyName "t3"),
                         [Elpi.API.ContextualConversion.TyName
                            elpi_constant_type_t3])]);
        pp = pp_t3;
        embed = elpi_embed_t3;
        readback = elpi_readback_t3
      }
    let elpi_t3 = Elpi.API.BuiltIn.MLDataC t3
    let elpi__t3__deep_copy =
      "func t3.copy t3 -> t3.\nt3.copy (a3 A0 A1) (a3 B0 B1) :- (t3.copy A0 B0), (t3.copy A1 B1).\nt3.copy (k A0) (k B0) :- (int.copy A0 B0).\nt3.copy (l3 A0 A1 A2) (l3 B0 B1 B2) :- (int.copy A0 B0), (string.copy A1 B1), (pi x\\ e3 x B1 B0 ==> t3.copy x x ==> (t3.copy (A2 x) (B2 x))).\n\n"
    class ctx_for_t3 (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_t3.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_c3) h s)
        method c3 = context_made_of_c3.Elpi.API.PPX.get s
      end
    let in_ctx_for_t3 :
      (Ctx_for_t3.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s ->
        let ctx = (new ctx_for_c3) h s in
        let (s, gls0) =
          Elpi.API.PPX.readback_context ~depth context_made_of_c3 ctx h c s in
        (s, ((new ctx_for_t3) h s), c, (List.concat [gls0]))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_t3; Elpi.API.BuiltIn.LPCode elpi__t3__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let t3 : 'c 'csts . (t3, #ctx_for_t3 as 'c, 'csts) ContextualConversion.t =
  t3
include
  struct
    class ctx_for_all (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state) =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_t1) h s)
        inherit ! ((ctx_for_t2) h s)
        inherit ! ((ctx_for_t3) h s)
      end
    let in_ctx_for_all :
      (ctx_for_all, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s ->
        let (s, _, c, gls0) = in_ctx_for_t1 ~depth h c s in
        let (s, _, c, gls1) = in_ctx_for_t2 ~depth h c s in
        let (s, _, c, gls2) = in_ctx_for_t3 ~depth h c s in
        (s, ((new ctx_for_all) h s), c, (List.concat [gls0; gls1; gls2]))
  end
open BuiltInPredicate.Notation
let all_to_string =
  BuiltInPredicate.ContextualPred
    ("all->string", in_ctx_for_all,
      (In
         (t1, "A",
           (In
              (t2, "B",
                (In
                   (t3, "C",
                     (Out
                        (BuiltInData.stringC, "S",
                          (Read
                             "three data types, each one under its own context"))))))))),
      (fun (a : t1) (b : t2) (c : t3) (_s : string BuiltInPredicate.oarg)
         ~depth:_ ctx (_cst : Data.constraints) (_state : State.t) ->
         let pp_ctx pp = RawData.Constants.Map.pp (PPX.pp_ctx_entry pp) in
         !:
           (Format.asprintf
              "@[<hov>%a |- %a@ ;@ %a |- %a@ ;@ %a |- %a@]@\n%!"
              (pp_ctx pp_c1) ctx#c1 t1.pp a (pp_ctx pp_c2) ctx#c2 t2.pp b
              (pp_ctx pp_c3) ctx#c3 t3.pp c)))
let builtin =
  let open BuiltIn in
    BuiltIn.declare ~file_name
      ((PPX.to_list declaration) @ [MLCode (all_to_string, DocAbove)])
let program =
  {|
main :-
  pi x y z\
    e1 x "x" 1 ==> e2 y "y" 2 ==> e3 z "z" 3 ==>
    t1.copy x x ==> t2.copy y y ==> t3.copy z z ==> (
      sigma A B C D E F K1 K2 K3\
        A = (a1 x x),
        B = (l2 2 "w" w\ a2 w y),
        C = (a3 z z),
        print {all->string A B C},
        t1.copy A D, t2.copy B E, t3.copy C F,
        print {all->string D E F},
        % k is the constructor of three types, the type tells which one is meant
        t1.copy (k 1) K1, t2.copy (k 2) K2, t3.copy (k 3) K3,
        K1 = k 1, K2 = k 2, K3 = k 3).
|}
let () = Ppx_tests_lib.run_program builtin program
