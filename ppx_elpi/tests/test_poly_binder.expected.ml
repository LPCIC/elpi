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
  | Entry of ((string)[@elpi.key ["term"; "A"]]) [@@elpi.index
                                                   (module String)][@@deriving
                                                                    (show,
                                                                    (elpi
                                                                    {
                                                                    declaration
                                                                    }))]
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
                   "(@[<2>Test_poly_binder.Entry@ ";
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
                 Elpi.API.Utils.type_error
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
                 then Elpi.API.Utils.type_error "not a bound variable";
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
                 | _ -> Elpi.API.Utils.type_error "not a bound variable")
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
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
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_tctx_Entryc)))
        | _ ->
            Elpi.API.Utils.type_error
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
               ~key:(Elpi.API.ContextualConversion.TyApp
                       ("term", (Elpi.API.ContextualConversion.TyName "A"),
                         []))
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
type 'a term =
  | Var of string [@elpi.var tctx]
  | Const of 'a 
  | Lam of string *
  (('a term)[@elpi.binder ["term"; "A"] tctx (fun s -> Entry s)]) [@@deriving
                                                                    (show,
                                                                    (elpi
                                                                    {
                                                                    declaration
                                                                    }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_term :
      'a .
        (Ppx_deriving_runtime.Format.formatter ->
           'a -> Ppx_deriving_runtime.unit)
          ->
          Ppx_deriving_runtime.Format.formatter ->
            'a term -> Ppx_deriving_runtime.unit
      =
      let __0 = pp_term in
      ((let open! Ppx_deriving_runtime in
          fun poly_a fmt ->
            function
            | Var a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_poly_binder.Var@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | Const a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_poly_binder.Const@ ";
                 (poly_a fmt) a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | Lam (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_poly_binder.Lam (@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__0 (fun fmt -> poly_a fmt) fmt) a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
        [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_term :
      'a .
        (Ppx_deriving_runtime.Format.formatter ->
           'a -> Ppx_deriving_runtime.unit)
          -> 'a term -> Ppx_deriving_runtime.string
      =
      fun poly_a x ->
        Ppx_deriving_runtime.Format.asprintf "%a" (pp_term poly_a) x[@@ocaml.warning
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
    let elpi_constant_constructor_term_Const = "const"
    let elpi_constant_constructor_term_Constc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_term_Const
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
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, #Ctx_for_term.t as 'c, 'csts)
          Elpi.API.ContextualConversion.embedding ->
          ('elpi__param__a term, #Ctx_for_term.t as 'c, 'csts)
            Elpi.API.ContextualConversion.embedding
      =
      fun elpi_embed_elpi__param__a ~depth:elpi__depth elpi__hyps
        elpi__constraints elpi__state elpi__fun_arg ->
        match elpi__fun_arg with
        | Var elpi__20 ->
            let (elpi__ctx2dbl, _) =
              Elpi.API.State.get elpi_tctx_state elpi__state in
            let elpi__key = (fun x -> x) elpi__20 in
            (if not (Elpi_tctx_Map.mem elpi__key elpi__ctx2dbl)
             then Elpi.API.Utils.error "Unbound variable";
             (elpi__state,
               (Elpi.API.RawData.mkBound
                  (Elpi_tctx_Map.find elpi__key elpi__ctx2dbl)), []))
        | Const elpi__23 ->
            let (elpi__state, elpi__25, elpi__24) =
              (fun ~depth h c s t -> elpi_embed_elpi__param__a ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__23 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_term_Constc [elpi__25]),
              (List.concat [elpi__24]))
        | Lam (elpi__26, elpi__27) ->
            let (elpi__state, elpi__30, elpi__28) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__26 in
            let elpi__ctx_entry = (fun s -> Entry s) elpi__26 in
            let elpi__ctx_key =
              elpi_tctx_to_key ~depth:elpi__depth elpi__ctx_entry in
            let elpi__ctx_entry =
              { Elpi.API.PPX.entry = elpi__ctx_entry; depth = elpi__depth } in
            let elpi__state =
              elpi_push_tctx ~depth:elpi__depth elpi__state elpi__ctx_key
                elpi__ctx_entry in
            let (elpi__state, elpi__32, elpi__29) =
              (fun ~depth h c s t ->
                 (elpi_embed_term
                    (fun ~depth h c s t ->
                       elpi_embed_elpi__param__a ~depth h c s t)) ~depth h c
                   s t) ~depth:(elpi__depth + 1) elpi__hyps elpi__constraints
                elpi__state elpi__27 in
            let elpi__31 = Elpi.API.RawData.mkLam elpi__32 in
            let elpi__state =
              elpi_pop_tctx ~depth:elpi__depth elpi__state elpi__ctx_key in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_term_Lamc [elpi__30; elpi__31]),
              (List.concat [elpi__28; elpi__29]))
    and elpi_readback_term :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, #Ctx_for_term.t as 'c, 'csts)
          Elpi.API.ContextualConversion.readback ->
          ('elpi__param__a term, #Ctx_for_term.t as 'c, 'csts)
            Elpi.API.ContextualConversion.readback
      =
      fun elpi_readback_elpi__param__a ~depth:elpi__depth elpi__hyps
        elpi__constraints elpi__state elpi__x ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.Const elpi__hd when elpi__hd >= 0 ->
            let (_, elpi__dbl2ctx) =
              Elpi.API.State.get elpi_tctx_state elpi__state in
            (if
               not
                 (Elpi.API.RawData.Constants.Map.mem elpi__hd elpi__dbl2ctx)
             then
               Elpi.API.Utils.error
                 (Format.asprintf "Unbound variable: %s in %a"
                    (Elpi.API.RawData.Constants.show elpi__hd)
                    (Elpi.API.RawData.Constants.Map.pp
                       (Elpi.API.PPX.pp_ctx_entry pp_tctx)) elpi__dbl2ctx);
             (let { Elpi.API.PPX.entry = elpi__entry; depth = elpi__depth } =
                Elpi.API.RawData.Constants.Map.find elpi__hd elpi__dbl2ctx in
              (elpi__state,
                (Var (elpi_tctx_to_key ~depth:elpi__depth elpi__entry)), [])))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_term_Constc ->
            let (elpi__state, elpi__15, elpi__14) =
              (fun ~depth h c s t ->
                 elpi_readback_elpi__param__a ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | [] ->
                 (elpi__state, (Const elpi__15), (List.concat [elpi__14]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_term_Constc)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_term_Lamc ->
            let (elpi__state, elpi__19, elpi__18) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | elpi__16::[] ->
                 let elpi__ctx_entry = (fun s -> Entry s) elpi__19 in
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
                 let (elpi__state, elpi__16, elpi__17) =
                   match Elpi.API.RawData.look ~depth:elpi__depth elpi__16
                   with
                   | Elpi.API.RawData.Lam elpi__bo ->
                       ((fun ~depth h c s t ->
                           (elpi_readback_term
                              (fun ~depth h c s t ->
                                 elpi_readback_elpi__param__a ~depth h c s t))
                             ~depth h c s t)) ~depth:(elpi__depth + 1)
                         elpi__hyps elpi__constraints elpi__state elpi__bo
                   | _ -> assert false in
                 let elpi__state =
                   elpi_pop_tctx ~depth:elpi__depth elpi__state elpi__ctx_key in
                 (elpi__state, (Lam (elpi__19, elpi__16)),
                   (List.concat [elpi__18; elpi__17]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_term_Lamc)))
        | _ ->
            Elpi.API.Utils.type_error
              (Format.asprintf "Not a constructor of type %s: %a" "term"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and term :
      'elpi__param__a 'c 'csts .
        ('elpi__param__a, #Ctx_for_term.t as 'c, 'csts)
          Elpi.API.ContextualConversion.t ->
          ('elpi__param__a term, #Ctx_for_term.t as 'c, 'csts)
            Elpi.API.ContextualConversion.t
      =
      fun elpi__param__a ->
        let kind =
          Elpi.API.ContextualConversion.TyApp
            ("term", (elpi__param__a.Elpi.API.ContextualConversion.ty), []) in
        {
          Elpi.API.ContextualConversion.ty = kind;
          pp_doc =
            (fun fmt () ->
               Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:0
                 ~ty:kind ~name:"const" ~doc:"Const"
                 ~args:[elpi__param__a.Elpi.API.ContextualConversion.ty];
               Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:0
                 ~ty:kind ~name:"lam" ~doc:"Lam"
                 ~args:[Elpi.API.BuiltInData.stringC.Elpi.API.ContextualConversion.ty;
                       Elpi.API.ContextualConversion.TyApp
                         ("->",
                           (Elpi.API.ContextualConversion.TyApp
                              ("term",
                                (Elpi.API.ContextualConversion.TyName "A"),
                                [])),
                           [Elpi.API.ContextualConversion.TyApp
                              (elpi_constant_type_term,
                                (elpi__param__a.Elpi.API.ContextualConversion.ty),
                                [])])]);
          pp = (pp_term elpi__param__a.pp);
          embed =
            (elpi_embed_term
               elpi__param__a.Elpi.API.ContextualConversion.embed);
          readback =
            (elpi_readback_term
               elpi__param__a.Elpi.API.ContextualConversion.readback)
        }
    let elpi_term =
      Elpi.API.BuiltIn.MLDataC (term (Elpi.API.BuiltInData.polyC "A"))
    let elpi__term__deep_copy =
      "func term.copy (func X0 -> Y0), term X0 -> term Y0.\nterm.copy F0 (const A0) (const B0) :- (F0 A0 B0).\nterm.copy F0 (lam A0 A1) (lam B0 B1) :- (string.copy A0 B0), (pi x\\ pi y\\ entry x B0 ==> entry y B0 ==> (term.copy F0 x y :- !) ==> ((term.copy F0) (A1 x) (B1 y))).\n\n"
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
let in_ctx_for_term : (ctx_for_term, 'csts) ContextualConversion.ctx_readback
  = in_ctx_for_term
let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)
let program =
  {|
main :-
  term.copy int.copy (lam "x" x\ lam "y" y\ const 1) T,
  T = lam "x" x\ lam "y" y\ const 1.
|}
let () = Ppx_tests_lib.run_program builtin program
