let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
module String =
  struct
    include String
    let pp fmt s = Format.fprintf fmt "%s" s
    let show = Format.asprintf "%a" pp
  end
type tctx =
  | Entry of ((string)[@elpi.key "term"]) [@@elpi.index (module String)]
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let pp_tctx :
      Ppx_deriving_runtime.Format.formatter ->
        tctx -> Ppx_deriving_runtime.unit
      =
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | Entry a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_record_binder.Entry@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])"))
      [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_tctx : tctx -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_tctx x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_tctx = "tctx"
    let elpi_constant_type_tctxc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_tctx
    let elpi_constant_constructor_tctx_Entry = "entry"
    let elpi_constant_constructor_tctx_Entryc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_tctx_Entry
    module Elpi_tctx_Map = (Elpi.API.Utils.Map.Make)(String)
    let elpi_tctx_state =
      Elpi.API.State.declare_component ~name:"tctx"
        ~pp:(fun fmt _ -> Format.fprintf fmt "TODO")
        ~init:(fun () ->
                 ((Elpi_tctx_Map.empty : Elpi.API.RawData.constant
                                           Elpi_tctx_Map.t),
                   (Elpi.API.RawData.Constants.Map.empty : tctx
                                                             Elpi.API.PPX.ctx_entry
                                                             Elpi.API.RawData.Constants.Map.t)))
        ~start:(fun x -> x) ()
    let elpi_tctx_to_key ~depth:_ elpi__fun_arg =
      match elpi__fun_arg with | Entry elpi__11 -> elpi__11
    let elpi_is_tctx { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x } =
      match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
      | Elpi.API.RawData.Const _ -> None
      | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
          if false || (elpi__hd == elpi_constant_constructor_tctx_Entryc)
          then
            (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
             | Elpi.API.RawData.Const x -> Some x
             | _ ->
                 Elpi.API.Error.error ~component:"ppx_elpi"
                   "context entry applied to a non bound variable")
          else None
      | _ -> None
    let elpi_push_tctx ~depth:elpi__depth elpi__state elpi__name
      elpi__ctx_item =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_tctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_tctx_Map.add elpi__name elpi__i elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item
          elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_tctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    let elpi_pop_tctx ~depth:elpi__depth elpi__state elpi__name =
      let (elpi__ctx2dbl, elpi__dbl2ctx) =
        Elpi.API.State.get elpi_tctx_state elpi__state in
      let elpi__i = elpi__depth in
      let elpi__ctx2dbl = Elpi_tctx_Map.remove elpi__name elpi__ctx2dbl in
      let elpi__dbl2ctx =
        Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
      let elpi__state =
        Elpi.API.State.set elpi_tctx_state elpi__state
          (elpi__ctx2dbl, elpi__dbl2ctx) in
      elpi__state
    module Ctx_for_tctx =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | (elpi__6, Entry elpi__5) ->
            let (elpi__state, elpi__9, elpi__7) =
              (fun ~depth elpi__hyps elpi__constraints elpi__state elpi__i ->
                 if elpi__i < 0
                 then
                   Elpi.API.Error.error ~component:"ppx_elpi"
                     "not a bound variable";
                 (elpi__state, (Elpi.API.RawData.mkConst elpi__i), []))
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__6 in
            let (elpi__state, elpi__10, elpi__8) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__5 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_tctx_Entryc [elpi__9; elpi__10]),
              (List.concat [elpi__7; elpi__8]))
    and elpi_readback_tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_tctx_Entryc ->
            let (elpi__state, elpi__4, elpi__3) =
              (fun ~depth elpi__hyps elpi__constraints elpi__state elpi__t ->
                 match Elpi.API.RawData.look ~depth elpi__t with
                 | Elpi.API.RawData.Const elpi__i when elpi__i >= 0 ->
                     (elpi__state, elpi__i, [])
                 | _ ->
                     Elpi.API.Error.error ~component:"ppx_elpi"
                       "not a bound variable") ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | elpi__1::[] ->
                 let (elpi__state, elpi__1, elpi__2) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__1 in
                 (elpi__state, (elpi__4, (Entry elpi__1)),
                   (List.concat [elpi__3; elpi__2]))
             | _ ->
                 Elpi.API.Error.error ~component:"ppx_elpi"
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_tctx_Entryc)))
        | _ ->
            Elpi.API.Error.error ~component:"ppx_elpi"
              (Format.asprintf "Not a constructor of type %s: %a" "tctx"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and tctx :
      'c 'csts .
        ((Elpi.API.RawData.constant * tctx), 'c, 'csts)
          Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "tctx" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             ();
             Elpi.API.PPX.Doc.context_entry fmt ~name:"entry" ~doc:"Entry"
               ~key:(Elpi.API.ContextualConversion.TyName "term")
               ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty]);
        pp = (fun fmt (_, x) -> pp_tctx fmt x);
        embed = elpi_embed_tctx;
        readback = elpi_readback_tctx
      }
    let context_made_of_tctx =
      {
        Elpi.API.PPX.is_entry_for_bound_var = elpi_is_tctx;
        to_key = elpi_tctx_to_key;
        push = elpi_push_tctx;
        pop = elpi_pop_tctx;
        conv = tctx;
        init =
          (fun state ->
             Elpi.API.State.set elpi_tctx_state state
               ((Elpi_tctx_Map.empty : Elpi.API.RawData.constant
                                         Elpi_tctx_Map.t),
                 (Elpi.API.RawData.Constants.Map.empty : tctx
                                                           Elpi.API.PPX.ctx_entry
                                                           Elpi.API.RawData.Constants.Map.t)));
        get =
          (fun state -> snd @@ (Elpi.API.State.get elpi_tctx_state state))
      }
    let elpi_tctx = Elpi.API.BuiltIn.MLDataC tctx
    class ctx_for_tctx (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_tctx.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_tctx :
      (Ctx_for_tctx.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s -> (s, ((new ctx_for_tctx) h s), c, (List.concat []))
    let () = Elpi.API.PPX.add_declarations declaration [elpi_tctx]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type term =
  | Var of {
  name: string } [@elpi.var tctx]
  | App of {
  fun_: term ;
  arg: term } 
  | Lam of
  {
  name: string ;
  body: ((term)[@elpi.binder "term" tctx (fun name -> Entry name)]) } 
[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_term :
      Ppx_deriving_runtime.Format.formatter ->
        term -> Ppx_deriving_runtime.unit
      =
      let __2 = pp_term
      and __1 = pp_term
      and __0 = pp_term in
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | Var { name = aname } ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "@[<2>Test_record_binder.Var {@,";
                 (Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "name";
                  (Ppx_deriving_runtime.Format.fprintf fmt "%S") aname;
                  Ppx_deriving_runtime.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime.Format.fprintf fmt "@]}")
            | App { fun_ = afun_; arg = aarg } ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "@[<2>Test_record_binder.App {@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "fun_";
                   (__0 fmt) afun_;
                   Ppx_deriving_runtime.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "arg";
                  (__1 fmt) aarg;
                  Ppx_deriving_runtime.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime.Format.fprintf fmt "@]}")
            | Lam { name = aname; body = abody } ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "@[<2>Test_record_binder.Lam {@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "name";
                   (Ppx_deriving_runtime.Format.fprintf fmt "%S") aname;
                   Ppx_deriving_runtime.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "body";
                  (__2 fmt) abody;
                  Ppx_deriving_runtime.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime.Format.fprintf fmt "@]}"))
        [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_term : term -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_term x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_term = "term"
    let elpi_constant_type_termc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_term
    let elpi_constant_constructor_term_Var = "var"
    let elpi_constant_constructor_term_Varc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Var
    let elpi_constant_constructor_term_App = "app"
    let elpi_constant_constructor_term_Appc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_App
    let elpi_constant_constructor_term_Lam = "lam"
    let elpi_constant_constructor_term_Lamc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Lam
    module Ctx_for_term =
      struct
        class type t =
          object
            inherit Elpi.API.PPX.ctx
            inherit Ctx_for_tctx.t
            method  tctx : tctx Elpi.API.PPX.ctx_field
          end
      end
    let rec elpi_embed_term :
      'c 'csts .
        (term, #Ctx_for_term.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | Var { name = elpi__22 } ->
            let (elpi__ctx2dbl, _) =
              Elpi.API.State.get elpi_tctx_state elpi__state in
            let elpi__key = (fun x -> x) elpi__22 in
            (if not (Elpi_tctx_Map.mem elpi__key elpi__ctx2dbl)
             then
               Elpi.API.Error.error ~component:"ppx_elpi" "Unbound variable";
             (elpi__state,
               (Elpi.API.RawData.mkBound
                  (Elpi_tctx_Map.find elpi__key elpi__ctx2dbl)), []))
        | App { fun_ = elpi__25; arg = elpi__26 } ->
            let (elpi__state, elpi__29, elpi__27) =
              (fun ~depth h c s t -> elpi_embed_term ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__25 in
            let (elpi__state, elpi__30, elpi__28) =
              (fun ~depth h c s t -> elpi_embed_term ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__26 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_term_Appc [elpi__29; elpi__30]),
              (List.concat [elpi__27; elpi__28]))
        | Lam { name = elpi__31; body = elpi__32 } ->
            let (elpi__state, elpi__35, elpi__33) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__31 in
            let elpi__ctx_entry = (fun name -> Entry name) elpi__31 in
            let elpi__ctx_key =
              elpi_tctx_to_key ~depth:elpi__depth elpi__ctx_entry in
            let elpi__ctx_entry =
              { Elpi.API.PPX.entry = elpi__ctx_entry; depth = elpi__depth } in
            let elpi__state =
              elpi_push_tctx ~depth:elpi__depth elpi__state elpi__ctx_key
                elpi__ctx_entry in
            let (elpi__state, elpi__37, elpi__34) =
              (fun ~depth h c s t -> elpi_embed_term ~depth h c s t)
                ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                elpi__state elpi__32 in
            let elpi__36 = Elpi.API.RawData.mkLam elpi__37 in
            let elpi__state =
              elpi_pop_tctx ~depth:elpi__depth elpi__state elpi__ctx_key in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_term_Lamc [elpi__35; elpi__36]),
              (List.concat [elpi__33; elpi__34]))
    and elpi_readback_term :
      'c 'csts .
        (term, #Ctx_for_term.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.Const elpi__hd when elpi__hd >= 0 ->
            let (_, elpi__dbl2ctx) =
              Elpi.API.State.get elpi_tctx_state elpi__state in
            (if
               not
                 (Elpi.API.RawData.Constants.Map.mem elpi__hd elpi__dbl2ctx)
             then
               Elpi.API.Error.error ~component:"ppx_elpi"
                 (Format.asprintf "Unbound variable: %s in %a"
                    (Elpi.API.RawData.Constants.show elpi__hd)
                    (Elpi.API.RawData.Constants.Map.pp
                       (Elpi.API.PPX.pp_ctx_entry pp_tctx)) elpi__dbl2ctx);
             (let { Elpi.API.PPX.entry = elpi__entry; depth = elpi__depth } =
                Elpi.API.RawData.Constants.Map.find elpi__hd elpi__dbl2ctx in
              (elpi__state,
                (Var
                   { name = (elpi_tctx_to_key ~depth:elpi__depth elpi__entry)
                   }), [])))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_term_Appc ->
            let (elpi__state, elpi__17, elpi__16) =
              (fun ~depth h c s t -> elpi_readback_term ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | elpi__14::[] ->
                 let (elpi__state, elpi__14, elpi__15) =
                   (fun ~depth h c s t -> elpi_readback_term ~depth h c s t)
                     ~depth:elpi__depth elpi__hyps elpi__constraints
                     elpi__state elpi__14 in
                 (elpi__state, (App { fun_ = elpi__17; arg = elpi__14 }),
                   (List.concat [elpi__16; elpi__15]))
             | _ ->
                 Elpi.API.Error.error ~component:"ppx_elpi"
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_term_Appc)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_term_Lamc ->
            let (elpi__state, elpi__21, elpi__20) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | elpi__18::[] ->
                 let elpi__ctx_entry = (fun name -> Entry name) elpi__21 in
                 let elpi__ctx_key =
                   elpi_tctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                 let elpi__ctx_entry =
                   {
                     Elpi.API.PPX.entry = elpi__ctx_entry;
                     depth = elpi__depth
                   } in
                 let elpi__state =
                   elpi_push_tctx ~depth:elpi__depth elpi__state
                     elpi__ctx_key elpi__ctx_entry in
                 let (elpi__state, elpi__18, elpi__19) =
                   match Elpi.API.RawData.look ~depth:elpi__depth elpi__18
                   with
                   | Elpi.API.RawData.Lam elpi__bo ->
                       ((fun ~depth h c s t ->
                           elpi_readback_term ~depth h c s t))
                         ~depth:(elpi__depth + 1) elpi__hyps
                         elpi__constraints elpi__state elpi__bo
                   | _ -> assert false in
                 let elpi__state =
                   elpi_pop_tctx ~depth:elpi__depth elpi__state elpi__ctx_key in
                 (elpi__state, (Lam { name = elpi__21; body = elpi__18 }),
                   (List.concat [elpi__20; elpi__19]))
             | _ ->
                 Elpi.API.Error.error ~component:"ppx_elpi"
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_term_Lamc)))
        | _ ->
            Elpi.API.Error.error ~component:"ppx_elpi"
              (Format.asprintf "Not a constructor of type %s: %a" "term"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and term :
      'c 'csts .
        (term, #Ctx_for_term.t as 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "term" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:3 ~variant:0
               ~ty:kind ~name:"app" ~doc:"App"
               ~args:[Elpi.API.ContextualConversion.TyName
                        elpi_constant_type_term;
                     Elpi.API.ContextualConversion.TyName
                       elpi_constant_type_term];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:3 ~variant:0
               ~ty:kind ~name:"lam" ~doc:"Lam"
               ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.ContextualConversion.TyApp
                       ("->", (Elpi.API.ContextualConversion.TyName "term"),
                         [Elpi.API.ContextualConversion.TyName
                            elpi_constant_type_term])]);
        pp = pp_term;
        embed = elpi_embed_term;
        readback = elpi_readback_term
      }
    let elpi_term = Elpi.API.BuiltIn.MLDataC term
    let elpi__term__deep_copy =
      "func term.copy term -> term.\nterm.copy (app A0 A1) (app B0 B1) :- (term.copy A0 B0), (term.copy A1 B1).\nterm.copy (lam A0 A1) (lam B0 B1) :- (string.copy A0 B0), (pi x\\ entry x B0 ==> term.copy x x ==> (term.copy (A1 x) (B1 x))).\n\n"
    class ctx_for_term (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_term.t =
      object (_)
        inherit  ((Elpi.API.PPX.ctx) h)
        inherit ! ((ctx_for_tctx) h s)
        method tctx = context_made_of_tctx.Elpi.API.PPX.get s
      end
    let in_ctx_for_term :
      (Ctx_for_term.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s ->
        let ctx = (new ctx_for_tctx) h s in
        let (s, gls0) =
          Elpi.API.PPX.readback_context ~depth context_made_of_tctx ctx h c s in
        (s, ((new ctx_for_term) h s), c, (List.concat [gls0]))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_term; Elpi.API.BuiltIn.LPCode elpi__term__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let term :
  'c 'csts . (term, #ctx_for_term as 'c, 'csts) ContextualConversion.t = term
let in_ctx_for_term : (ctx_for_term, 'csts) ContextualConversion.ctx_readback
  = in_ctx_for_term
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let program =
  {|
main :-
  term.copy (lam "x" x\ app x x) Y,
  Y = lam "x" y\ app y y.
|}
let () = Ppx_tests_lib.run_program builtin program
