let file_name = Sys.argv.(1)
open Elpi.API
let declaration = PPX.empty_declaration ()
type color =
  | Red 
  | Green 
  | Blue of int [@@deriving (show, (elpi { declaration }))]
include
  struct
    [@@@ocaml.warning "-60"]
    let pp_color :
      Ppx_deriving_runtime.Format.formatter ->
        color -> Ppx_deriving_runtime.unit
      =
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | Red ->
                Ppx_deriving_runtime.Format.pp_print_string fmt
                  "Test_mixed_conversions_pred.Red"
            | Green ->
                Ppx_deriving_runtime.Format.pp_print_string fmt
                  "Test_mixed_conversions_pred.Green"
            | Blue a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_mixed_conversions_pred.Blue@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%d") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])"))
      [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_color : color -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_color x[@@ocaml.warning
                                                                    "-32"]
    [@@@warning "-26-27-32-39-60"]
    let elpi_constant_type_color = "color"
    let elpi_constant_type_colorc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_type_color
    let elpi_constant_constructor_color_Red = "red"
    let elpi_constant_constructor_color_Redc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_color_Red
    let elpi_constant_constructor_color_Green = "green"
    let elpi_constant_constructor_color_Greenc =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_color_Green
    let elpi_constant_constructor_color_Blue = "blue"
    let elpi_constant_constructor_color_Bluec =
      Elpi.API.RawData.Constants.declare_global_symbol
        elpi_constant_constructor_color_Blue
    module Ctx_for_color =
      struct class type t = object inherit Elpi.API.PPX.ctx end end
    let rec elpi_embed_color :
      'c 'csts . (color, 'c, 'csts) Elpi.API.ContextualConversion.embedding =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
        elpi__fun_arg ->
        match elpi__fun_arg with
        | Red ->
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_color_Redc []), (List.concat []))
        | Green ->
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_color_Greenc []),
              (List.concat []))
        | Blue elpi__3 ->
            let (elpi__state, elpi__5, elpi__4) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.embed
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__3 in
            (elpi__state,
              (Elpi.API.RawData.mkAppGlobalL
                 elpi_constant_constructor_color_Bluec [elpi__5]),
              (List.concat [elpi__4]))
    and elpi_readback_color :
      'c 'csts . (color, 'c, 'csts) Elpi.API.ContextualConversion.readback =
      fun ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state elpi__x
        ->
        match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
        | Elpi.API.RawData.Const elpi__hd when
            elpi__hd == elpi_constant_constructor_color_Redc ->
            (elpi__state, Red, [])
        | Elpi.API.RawData.Const elpi__hd when
            elpi__hd == elpi_constant_constructor_color_Greenc ->
            (elpi__state, Green, [])
        | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
            elpi__hd == elpi_constant_constructor_color_Bluec ->
            let (elpi__state, elpi__2, elpi__1) =
              (fun ~depth h c s t ->
                 Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.readback
                   ~depth h c s t) ~depth:elpi__depth elpi__hyps
                elpi__constraints elpi__state elpi__x in
            (match elpi__xs with
             | [] -> (elpi__state, (Blue elpi__2), (List.concat [elpi__1]))
             | _ ->
                 Elpi.API.Utils.type_error
                   ("Not enough arguments to constructor: " ^
                      (Elpi.API.RawData.Constants.show
                         elpi_constant_constructor_color_Bluec)))
        | _ ->
            Elpi.API.Utils.type_error
              (Format.asprintf "Not a constructor of type %s: %a" "color"
                 (Elpi.API.RawPp.term elpi__depth) elpi__x)
    and color : 'c 'csts . (color, 'c, 'csts) Elpi.API.ContextualConversion.t
      =
      let kind = Elpi.API.ContextualConversion.TyName "color" in
      {
        Elpi.API.ContextualConversion.ty = kind;
        pp_doc =
          (fun fmt () ->
             Elpi.API.PPX.Doc.kind fmt kind ~doc:"";
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:0
               ~ty:kind ~name:"red" ~doc:"Red" ~args:[];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:0
               ~ty:kind ~name:"green" ~doc:"Green" ~args:[];
             Elpi.API.PPX.Doc.constructor fmt ~max_name_len:5 ~variant:0
               ~ty:kind ~name:"blue" ~doc:"Blue"
               ~args:[Elpi.API.BuiltInData.intC.Elpi.API.ContextualConversion.ty]);
        pp = pp_color;
        embed = elpi_embed_color;
        readback = elpi_readback_color
      }
    let elpi_color = Elpi.API.BuiltIn.MLDataC color
    let elpi__color__deep_copy =
      "func color.copy color -> color.\ncolor.copy red red.\ncolor.copy green green.\ncolor.copy (blue A0) (blue B0) :- (int.copy A0 B0).\n\n"
    class ctx_for_color (h : Elpi.API.Data.hyps)  (s : Elpi.API.Data.state)
      : Ctx_for_color.t = object (_) inherit  ((Elpi.API.PPX.ctx) h) end
    let in_ctx_for_color :
      (Ctx_for_color.t, 'csts) Elpi.API.ContextualConversion.ctx_readback =
      fun ~depth h c s -> (s, ((new ctx_for_color) h s), c, (List.concat []))
    let () =
      Elpi.API.PPX.add_declarations declaration
        [elpi_color; Elpi.API.BuiltIn.LPCode elpi__color__deep_copy]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
let color : 'c 'csts . (color, 'c, 'csts) ContextualConversion.t = color
type lam =
  | V of string 
  | Ap of lam * lam 
  | Lm of string * lam [@@deriving show]
include
  struct
    let rec pp_lam :
      Ppx_deriving_runtime.Format.formatter ->
        lam -> Ppx_deriving_runtime.unit
      =
      let __2 = pp_lam
      and __1 = pp_lam
      and __0 = pp_lam in
      ((let open! Ppx_deriving_runtime in
          fun fmt ->
            function
            | V a0 ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_mixed_conversions_pred.V@ ";
                 (Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime.Format.fprintf fmt "@])")
            | Ap (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_mixed_conversions_pred.Ap (@,";
                 ((__0 fmt) a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__1 fmt) a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]")
            | Lm (a0, a1) ->
                (Ppx_deriving_runtime.Format.fprintf fmt
                   "(@[<2>Test_mixed_conversions_pred.Lm (@,";
                 ((Ppx_deriving_runtime.Format.fprintf fmt "%S") a0;
                  Ppx_deriving_runtime.Format.fprintf fmt ",@ ";
                  (__2 fmt) a1);
                 Ppx_deriving_runtime.Format.fprintf fmt "@,))@]"))
        [@ocaml.warning "-A"])[@@ocaml.warning "-39"]
    let show_lam : lam -> Ppx_deriving_runtime.string =
      fun x -> Ppx_deriving_runtime.Format.asprintf "%a" pp_lam x[@@ocaml.warning
                                                                   "-32"]
  end[@@ocaml.doc "@inline"][@@merlin.hide ]
type context = string RawData.Constants.Map.t
let c_ap = RawData.Constants.declare_global_symbol "ap"
let c_lm = RawData.Constants.declare_global_symbol "lm"
let c_known = RawData.Constants.declare_global_symbol "known"
let known_ctx : (context, Data.constraints) ContextualConversion.ctx_readback
  =
  fun ~depth hyps csts state ->
    let (ctx, state, gls) =
      List.fold_left
        (fun (ctx, state, gls) { RawData.hdepth = hdepth; hsrc } ->
           match RawData.look ~depth:hdepth hsrc with
           | RawData.App (c, x, s::[]) when c = c_known ->
               (match RawData.look ~depth:hdepth x with
                | RawData.Const l ->
                    let (state, s, g) =
                      BuiltInData.string.readback ~depth:hdepth state s in
                    ((RawData.Constants.Map.add l s ctx), state, (g @ gls))
                | _ -> (ctx, state, gls))
           | _ -> (ctx, state, gls)) (RawData.Constants.Map.empty, state, [])
        (RawData.of_hyps hyps) in
    (state, ctx, csts, gls)
let level_of (ctx : context) name =
  match RawData.Constants.Map.fold
          (fun l n acc -> if n = name then Some l else acc) ctx None
  with
  | Some l -> l
  | None -> Utils.type_error ("unbound variable " ^ name)
let rec embed_lam ~depth (ctx : context) csts state =
  function
  | V s -> (state, (RawData.mkBound (level_of ctx s)), [])
  | Ap (a, b) ->
      let (state, a, ga) = embed_lam ~depth ctx csts state a in
      let (state, b, gb) = embed_lam ~depth ctx csts state b in
      (state, (RawData.mkAppGlobal c_ap a [b]), (ga @ gb))
  | Lm (name, t) ->
      let (state, s, gs) = BuiltInData.string.embed ~depth state name in
      let ctx = RawData.Constants.Map.add depth name ctx in
      let (state, t, g) = embed_lam ~depth:(depth + 1) ctx csts state t in
      (state, (RawData.mkAppGlobal c_lm s [RawData.mkLam t]), (gs @ g))
let rec readback_lam ~depth (ctx : context) csts state t =
  match RawData.look ~depth t with
  | RawData.Const l ->
      (match RawData.Constants.Map.find_opt l ctx with
       | Some s -> (state, (V s), [])
       | None -> Utils.type_error "unbound variable")
  | RawData.App (c, a, b::[]) when c = c_ap ->
      let (state, a, ga) = readback_lam ~depth ctx csts state a in
      let (state, b, gb) = readback_lam ~depth ctx csts state b in
      (state, (Ap (a, b)), (ga @ gb))
  | RawData.App (c, s, f::[]) when c = c_lm ->
      let (state, s, gs) = BuiltInData.string.readback ~depth state s in
      (match RawData.look ~depth f with
       | RawData.Lam body ->
           let ctx = RawData.Constants.Map.add depth s ctx in
           let (state, t, g) =
             readback_lam ~depth:(depth + 1) ctx csts state body in
           (state, (Lm (s, t)), (gs @ g))
       | _ -> Utils.type_error "lm expects a lambda")
  | _ -> Utils.type_error "not a lam"
let lam : (lam, context, Data.constraints) ContextualConversion.t =
  {
    ty = (TyName "lam");
    pp = pp_lam;
    pp_doc =
      (fun fmt () ->
         Format.fprintf fmt "data lam.@\n";
         Format.fprintf fmt "builtin symb ap : lam -> lam -> lam = \"0\".@\n";
         Format.fprintf fmt
           "builtin symb lm : string -> (lam -> lam) -> lam = \"0\".@\n@\n");
    embed = embed_lam;
    readback = readback_lam
  }
open BuiltInPredicate.Notation
let describe =
  BuiltInPredicate.Pred
    ("describe",
      (CIn
         (lam, "T",
           (CIn
              (color, "C",
                (Out
                   (BuiltInData.string, "S",
                     (COut
                        (lam, "R",
                          (Read
                             (known_ctx,
                               "describes a term and a colour, and applies the term to y")))))))))),
      (fun (t : lam) (c : color) (_s : string BuiltInPredicate.oarg)
         (_r : lam BuiltInPredicate.oarg) ~depth:_ (ctx : context)
         (_cst : Data.constraints) (_state : State.t) ->
         (!:
            (Format.asprintf "%a ; %a ; known: %s" pp_color c pp_lam t
               (String.concat ", "
                  (List.map snd (RawData.Constants.Map.bindings ctx)))))
           +! (Ap (t, (V "y")))))
let builtin =
  let open BuiltIn in
    BuiltIn.declare ~file_name
      ((PPX.to_list declaration) @
         [MLDataC lam;
         LPCode "builtin func known lam -> string.";
         MLCode (describe, DocAbove)])
let program =
  {|
main :-
  pi a b\
    known a "x" ==> known b "y" ==>
      sigma S R\
        describe (lm "z" z\ ap z (ap a b)) (blue 3) S R,
        print S,
        % the name y is mapped back to the constant b by the context
        print R.
|}
let () = Ppx_tests_lib.run_program builtin program
