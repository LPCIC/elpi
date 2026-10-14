let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type rat = {
  num: int ;
  den: int }[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let pp_rat :
      Ppx_deriving_runtime.Format.formatter ->
        rat -> Ppx_deriving_runtime.unit
      =
      ((let open! Ppx_deriving_runtime in
          fun fmt x ->
            Ppx_deriving_runtime.Format.fprintf fmt "@[<2>{ ";
            ((Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ "
                "Test_thomas.num";
              (Ppx_deriving_runtime.Format.fprintf fmt "%d") x.num;
              Ppx_deriving_runtime.Format.fprintf fmt "@]");
             Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
             Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "den";
             (Ppx_deriving_runtime.Format.fprintf fmt "%d") x.den;
             Ppx_deriving_runtime.Format.fprintf fmt "@]");
            Ppx_deriving_runtime.Format.fprintf fmt "@ }@]")
      [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_rat : rat -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_rat x[@@ocaml.warning
                                                                   "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_rat = "rat"
    let elpi_constant_type_ratc =
      Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_rat
    let elpi_constant_constructor_rat_rat = "rat"
    let elpi_constant_constructor_rat_ratc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_rat_rat
    module Ctx_for_rat =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_rat :
      'c 'csts . (rat, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | { num = elpi__5; den = elpi__6 } ->
            let (elpi__state, elpi__9, elpi__7) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__5 in
            let (elpi__state, elpi__10, elpi__8) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__6 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_rat_ratc [elpi__9; elpi__10]),
              (List.concat [elpi__7; elpi__8]))
    and elpi_readback_rat :
      'c 'csts . (rat, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_rat_ratc ->
            let (elpi__state, elpi__4, elpi__3) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | elpi__1::[] ->
                 let (elpi__state, elpi__1, elpi__2) =
                   (fun ~depth h c s t ->
                      Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                        ~depth h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__1 in
                 (elpi__state, { num = elpi__4; den = elpi__1 },
                   (List.concat [elpi__3; elpi__2]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_rat_ratc)))
        | _ ->
            Elpi.API.Utils.type_error
              (Format.asprintf "Not a constructor of type %s: %a" "rat"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and rat : 'c 'csts . (rat, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "rat" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:3 ~variant:0
               ~ty:kind ~name:"rat" ~doc:"rat"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty;
                     Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty]);
        pp = pp_rat;
        embed = elpi_embed_rat;
        readback = elpi_readback_rat
      }
    let elpi_rat = Elpi.API.BuiltIn.MLDataC rat
    let elpi__rat__deep_copy =
      "func rat.copy rat -> rat.\nrat.copy (rat A0 A1) (rat B0 B1) :- (int.copy A0 B0), (int.copy A1 B1).\n\n"
    class ctx_for_rat (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_rat.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_rat :
      (Ctx_for_rat.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s -> (s, ((new ctx_for_rat) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_rat; Elpi.API.BuiltIn.LPCode elpi__rat__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type poly =
  | Const of rat [@elpi.code "pcst"]
  | Var of int [@elpi.code "variable"]
  | Add of poly * poly 
  | Mul of poly * poly [@@deriving (show, (elpi { declaration }))][@@elpi.type_code
                                                                    "polyT"]
include
  struct
    [@@@ocaml.warning "-60"]
    let rec pp_poly :
      Ppx_deriving_runtime.Format.formatter ->
        poly -> Ppx_deriving_runtime.unit
      =
      let __4 = pp_poly
      and __3 = pp_poly
      and __2 = pp_poly
      and __1 = pp_poly
      and __0 = pp_rat in
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | Const a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_thomas.Const@ ";
                 (__0 fmt) a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | Var a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_thomas.Var@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | Add (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_thomas.Add (@,";
                 ((__1 fmt) a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__2 fmt) a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
            | Mul (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_thomas.Mul (@,";
                 ((__3 fmt) a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__4 fmt) a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
        [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_poly : poly -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_poly x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_poly = "polyT"
    let elpi_constant_type_polyc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_poly
    let elpi_constant_constructor_poly_Const = "pcst"
    let elpi_constant_constructor_poly_Constc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_poly_Const
    let elpi_constant_constructor_poly_Var = "variable"
    let elpi_constant_constructor_poly_Varc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_poly_Var
    let elpi_constant_constructor_poly_Add = "add"
    let elpi_constant_constructor_poly_Addc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_poly_Add
    let elpi_constant_constructor_poly_Mul = "mul"
    let elpi_constant_constructor_poly_Mulc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_poly_Mul
    module Ctx_for_poly =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_poly :
      'c 'csts . (poly, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | Const elpi__23 ->
            let (elpi__state, elpi__25, elpi__24) =
              (fun ~depth h c s t ->
                 rat.Elpi.API.ContextualConversion.embed ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__23 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_poly_Constc [elpi__25]),
              (List.concat [elpi__24]))
        | Var elpi__26 ->
            let (elpi__state, elpi__28, elpi__27) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__26 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_poly_Varc [elpi__28]),
              (List.concat [elpi__27]))
        | Add (elpi__29, elpi__30) ->
            let (elpi__state, elpi__33, elpi__31) =
              (fun ~depth h c s t -> elpi_embed_poly ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__29 in
            let (elpi__state, elpi__34, elpi__32) =
              (fun ~depth h c s t -> elpi_embed_poly ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__30 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_poly_Addc [elpi__33; elpi__34]),
              (List.concat [elpi__31; elpi__32]))
        | Mul (elpi__35, elpi__36) ->
            let (elpi__state, elpi__39, elpi__37) =
              (fun ~depth h c s t -> elpi_embed_poly ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__35 in
            let (elpi__state, elpi__40, elpi__38) =
              (fun ~depth h c s t -> elpi_embed_poly ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__36 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_poly_Mulc [elpi__39; elpi__40]),
              (List.concat [elpi__37; elpi__38]))
    and elpi_readback_poly :
      'c 'csts . (poly, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_poly_Constc ->
            let (elpi__state, elpi__12, elpi__11) =
              (fun ~depth h c s t ->
                 rat.Elpi.API.ContextualConversion.readback ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | [] ->
                 (elpi__state, (Const elpi__12), (List.concat [elpi__11]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_poly_Constc)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_poly_Varc ->
            let (elpi__state, elpi__14, elpi__13) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | [] -> (elpi__state, (Var elpi__14), (List.concat [elpi__13]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_poly_Varc)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_poly_Addc ->
            let (elpi__state, elpi__18, elpi__17) =
              (fun ~depth h c s t -> elpi_readback_poly ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | elpi__15::[] ->
                 let (elpi__state, elpi__15, elpi__16) =
                   (fun ~depth h c s t -> elpi_readback_poly ~depth h c s t)
                     ~depth:elpi__depth elpi__hyps elpi__constraints
                     elpi__state elpi__15 in
                 (elpi__state, (Add (elpi__18, elpi__15)),
                   (List.concat [elpi__17; elpi__16]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_poly_Addc)))
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_poly_Mulc ->
            let (elpi__state, elpi__22, elpi__21) =
              (fun ~depth h c s t -> elpi_readback_poly ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | elpi__19::[] ->
                 let (elpi__state, elpi__19, elpi__20) =
                   (fun ~depth h c s t -> elpi_readback_poly ~depth h c s t)
                     ~depth:elpi__depth elpi__hyps elpi__constraints
                     elpi__state elpi__19 in
                 (elpi__state, (Mul (elpi__22, elpi__19)),
                   (List.concat [elpi__21; elpi__20]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_poly_Mulc)))
        | _ ->
            Elpi.API.Utils.type_error
              (Format.asprintf "Not a constructor of type %s: %a" "poly"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and poly : 'c 'csts . (poly, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "polyT" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:8 ~variant:0
               ~ty:kind ~name:"pcst" ~doc:"Const"
               ~args:[rat.Elpi.API.ContextualConversion.ty];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:8 ~variant:0
               ~ty:kind ~name:"variable" ~doc:"Var"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:8 ~variant:0
               ~ty:kind ~name:"add" ~doc:"Add"
               ~args:[Elpi.API.ContextualConversion.TyName
                        elpi_constant_type_poly;
                     Elpi.API.ContextualConversion.TyName
                       elpi_constant_type_poly];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:8 ~variant:0
               ~ty:kind ~name:"mul" ~doc:"Mul"
               ~args:[Elpi.API.ContextualConversion.TyName
                        elpi_constant_type_poly;
                     Elpi.API.ContextualConversion.TyName
                       elpi_constant_type_poly]);
        pp = pp_poly;
        embed = elpi_embed_poly;
        readback = elpi_readback_poly
      }
    let elpi_poly = Elpi.API.BuiltIn.MLDataC poly
    let elpi__poly__deep_copy =
      "func polyT.copy polyT -> polyT.\npolyT.copy (pcst A0) (pcst B0) :- (rat.copy A0 B0).\npolyT.copy (variable A0) (variable B0) :- (int.copy A0 B0).\npolyT.copy (add A0 A1) (add B0 B1) :- (polyT.copy A0 B0), (polyT.copy A1 B1).\npolyT.copy (mul A0 A1) (mul B0 B1) :- (polyT.copy A0 B0), (polyT.copy A1 B1).\n\n"
    class ctx_for_poly (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_poly.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_poly :
      (Ctx_for_poly.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s -> (s, ((new ctx_for_poly) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_poly; Elpi.API.BuiltIn.LPCode elpi__poly__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type monomial = {
  coef: rat ;
  exps: (int * int) list }[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let pp_monomial :
      Ppx_deriving_runtime.Format.formatter ->
        monomial -> Ppx_deriving_runtime.unit
      =
      let __0 = pp_rat in
      ((let open! Ppx_deriving_runtime in
          fun fmt x ->
            Ppx_deriving_runtime.Format.fprintf fmt "@[<2>{ ";
            ((Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ "
                "Test_thomas.coef";
              (__0 fmt) x.coef;
              Ppx_deriving_runtime.Format.fprintf fmt "@]");
             Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
             Ppx_deriving_runtime.Format.fprintf fmt "@[%s =@ " "exps";
             ((fun x ->
                 Ppx_deriving_runtime.Format.fprintf fmt "@[<2>[";
                 ignore
                   (List.fold_left
                      (fun sep x ->
                         if sep
                         then Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
                         ((fun (a0, a1) ->
                             Ppx_deriving_runtime.Format.fprintf fmt "(@[";
                             ((Ppx_deriving_runtime.Format.fprintf fmt "%d")
                                a0;
                              Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                              (Ppx_deriving_runtime.Format.fprintf fmt "%d")
                                a1);
                             Ppx_deriving_runtime.Format.fprintf fmt "@])"))
                           x;
                         true) false x);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,]@]")) x.exps;
             Ppx_deriving_runtime.Format.fprintf fmt "@]");
            Ppx_deriving_runtime.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_monomial : monomial -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_monomial x
      [@@ocaml.warning "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_monomial = "monomial"
    let elpi_constant_type_monomialc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_monomial
    let elpi_constant_constructor_monomial_monomial = "monomial"
    let elpi_constant_constructor_monomial_monomialc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_monomial_monomial
    module Ctx_for_monomial =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_monomial :
      'c 'csts .
        (monomial, 'c, 'csts) Elpi.API.ContextualConversion.embedding
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | { coef = elpi__45; exps = elpi__46 } ->
            let (elpi__state, elpi__49, elpi__47) =
              (fun ~depth h c s t ->
                 rat.Elpi.API.ContextualConversion.embed ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__45 in
            let (elpi__state, elpi__50, elpi__48) =
              (fun ~depth h c s t ->
                 (let embed =
                    Elpi.Builtin.PPX.embed_pair
                      Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                      Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed in
                  fun ~depth h c s l ->
                    let (s, l, eg) =
                      Elpi.API.Utils.map_acc (embed ~depth h c) s l in
                    (s, (Elpi.API.Utils.list_to_lp_list l), eg)) ~depth h c s
                   t) ~depth:elpi__depth elpi__hyps elpi__constraints
                elpi__state elpi__46 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_monomial_monomialc
                 [elpi__49; elpi__50]), (List.concat [elpi__47; elpi__48]))
    and elpi_readback_monomial :
      'c 'csts . (monomial, 'c, 'csts) Elpi.API.ContextualConversion.readback
      =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_monomial_monomialc ->
            let (elpi__state, elpi__44, elpi__43) =
              (fun ~depth h c s t ->
                 rat.Elpi.API.ContextualConversion.readback ~depth h c s t)
                ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                elpi__x in
            (match elpi__xs with
             | elpi__41::[] ->
                 let (elpi__state, elpi__41, elpi__42) =
                   (fun ~depth h c s t ->
                      (let readback =
                         Elpi.Builtin.PPX.readback_pair
                           Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                           Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback in
                       fun ~depth h c s t ->
                         Elpi.API.Utils.map_acc (readback ~depth h c) s
                           (Elpi.API.Utils.lp_list_to_list ~depth t)) ~depth
                        h c s t) ~depth:elpi__depth elpi__hyps
                     elpi__constraints elpi__state elpi__41 in
                 (elpi__state, { coef = elpi__44; exps = elpi__41 },
                   (List.concat [elpi__43; elpi__42]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_monomial_monomialc)))
        | _ ->
            Elpi.API.Utils.type_error
              (Format.asprintf "Not a constructor of type %s: %a" "monomial"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and monomial :
      'c 'csts . (monomial, 'c, 'csts) Elpi.API.ContextualConversion.t =
      let kind = Elpi.API.ContextualConversion.TyName "monomial" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:8 ~variant:0
               ~ty:kind ~name:"monomial" ~doc:"monomial"
               ~args:[rat.Elpi.API.ContextualConversion.ty;
                     Elpi.API.ContextualConversion.TyApp
                       ("list",
                         (Elpi.API.ContextualConversion.TyApp
                            ("pair",
                              (Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty),
                              [Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty])),
                         [])]);
        pp = pp_monomial;
        embed = elpi_embed_monomial;
        readback = elpi_readback_monomial
      }
    let elpi_monomial = Elpi.API.BuiltIn.MLDataC monomial
    let elpi__monomial__deep_copy =
      "func monomial.copy monomial -> monomial.\nmonomial.copy (monomial A0 A1) (monomial B0 B1) :- (rat.copy A0 B0), ((list.copy (pair.copy int.copy int.copy)) A1 B1).\n\n"
    class ctx_for_monomial (h : Elpi.API.Data.hyps) 
      (s : Elpi.API.Data.state) : Ctx_for_monomial.t =
      object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_monomial :
      (Ctx_for_monomial.t, 'csts) Elpi.API.ContextualConversion.ctx_readback
      =
      fun ~depth h c s ->
        (s, ((new ctx_for_monomial) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_monomial; Elpi.API.BuiltIn.LPCode elpi__monomial__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type mpoly = monomial list[@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let pp_mpoly :
      Ppx_deriving_runtime.Format.formatter ->
        mpoly -> Ppx_deriving_runtime.unit
      =
      let __0 = pp_monomial in
      ((let open! Ppx_deriving_runtime in
          fun fmt x ->
            Ppx_deriving_runtime.Format.fprintf fmt "@[<2>[";
            ignore
              (List.fold_left
                 (fun sep x ->
                    if sep then Ppx_deriving_runtime.Format.fprintf fmt ";@ ";
                    (__0 fmt) x;
                    true) false x);
            Ppx_deriving_runtime.Format.fprintf fmt "@,]@]")
        [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_mpoly : mpoly -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_mpoly x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_mpoly = "mpoly"
    let elpi_constant_type_mpolyc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_mpoly
    module Ctx_for_mpoly =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_mpoly :
      'c 'csts . (mpoly, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth h c s t ->
        (let embed = monomial.Elpi.API.ContextualConversion.embed in
         fun ~depth h c s l ->
           let (s, l, eg) = Elpi.API.Utils.map_acc (embed ~depth h c) s l in
           (s, (Elpi.API.Utils.list_to_lp_list l), eg)) ~depth h c s t
    and elpi_readback_mpoly :
      'c 'csts . (mpoly, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth h c s t ->
        (let readback = monomial.Elpi.API.ContextualConversion.readback in
         fun ~depth h c s t ->
           Elpi.API.Utils.map_acc (readback ~depth h c) s
             (Elpi.API.Utils.lp_list_to_list ~depth t)) ~depth h c s t
    and mpoly : 'c 'csts . (mpoly, 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "mpoly" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc = (fun fmt () -> Elpi.API.PPX.Doc.kind fmt kind ~doc:""; ());
        pp = pp_mpoly;
        embed = elpi_embed_mpoly;
        readback = elpi_readback_mpoly
      }
    let elpi_mpoly =
      Elpi.API.BuiltIn.LPCode
        ("typeabbrev " ^
           ("mpoly" ^
              (" " ^
                 (((let open Elpi.API.PPX.Doc in show_ty_ast ~prec:AppArg) @@
                     (Elpi.API.BuiltInData.listC monomial).Elpi.API.ContextualConversion.ty)
                    ^ (". % " ^ "mpoly")))))
    let elpi__mpoly__deep_copy =
      "func mpoly.copy mpoly -> mpoly.\nmpoly.copy A B :- ((list.copy monomial.copy) A B)."
    class ctx_for_mpoly (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_mpoly.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_mpoly :
      (Ctx_for_mpoly.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s -> (s, ((new ctx_for_mpoly) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_mpoly; Elpi.API.BuiltIn.LPCode elpi__mpoly__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let _ : (rat, _, _) ContextualConversion.t = rat
let _ : (poly, _, _) ContextualConversion.t = poly
let _ : (monomial, _, _) ContextualConversion.t = monomial
let _ : (mpoly, _, _) ContextualConversion.t = mpoly
open BuiltInPredicate.Notation
let poly_to_str =
  let open BuiltIn in
    let open BuiltInPredicate in
      MLCode
        ((ContextualPred
            ("poly->str", in_ctx_for_poly,
              (In
                 (poly, "P",
                   (Out
                      (BuiltInData.stringC, "S",
                        (Read "prints a polynomial"))))),
              (fun (p : poly) (_s : string BuiltInPredicate.oarg) ~depth:_
                 _ctx (_cst : Data.constraints) (_state : State.t) ->
                 !: (show_poly p)))), DocAbove)
let builtin =
  BuiltIn.declare ~file_name ((PPX.to_list declaration) @ [poly_to_str])
let () = Ppx_tests_lib.check_declarations builtin
