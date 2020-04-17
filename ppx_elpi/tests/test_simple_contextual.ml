let declaration = ref []

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

let pp_ctx _ _ = ()
type ctx = Entry of (string[@elpi.key]) * bool
  [@@elpi.index (module String)]
[@@deriving_inline elpi { declaration }]
let _ = fun (_ : ctx) -> ()
[@@@warning "-26-27-32-39-60"]
let elpi_constant_type_ctx = "ctx"
let _ = elpi_constant_type_ctx
let elpi_constant_type_ctxc =
  Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_ctx
let _ = elpi_constant_type_ctxc
let elpi_constant_constructor_ctx_Entry = "entry"
let _ = elpi_constant_constructor_ctx_Entry
let elpi_constant_constructor_ctx_Entryc =
  Elpi.API.RawData.Constants.declare_global_symbol
    elpi_constant_constructor_ctx_Entry
let _ = elpi_constant_constructor_ctx_Entryc
module Elpi_ctx_Map = (Elpi.API.Utils.Map.Make)(String)
let elpi_ctx_state =
  Elpi.API.State.declare ~name:"ctx"
    ~pp:(fun fmt -> fun _ -> Format.fprintf fmt "TODO")
    ~init:(fun () ->
             ((Elpi_ctx_Map.empty : Elpi.API.RawData.constant Elpi_ctx_Map.t),
               (Elpi.API.RawData.Constants.Map.empty : ctx
                                                         Elpi.API.Conversion.ctx_entry
                                                         Elpi.API.RawData.Constants.Map.t)))
let _ = elpi_ctx_state
let elpi_ctx_to_key ~depth:_  = function | Entry (elpi__16, _) -> elpi__16
let _ = elpi_ctx_to_key
let elpi_is_ctx { Elpi.API.Data.hdepth = elpi__depth; hsrc = elpi__x } =
  match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
  | Elpi.API.RawData.Const _ -> None
  | Elpi.API.RawData.App (elpi__hd, elpi__idx, _) ->
      if false || (elpi__hd == elpi_constant_constructor_ctx_Entryc)
      then
        (match Elpi.API.RawData.look ~depth:elpi__depth elpi__idx with
         | Elpi.API.RawData.Const x -> Some x
         | _ ->
             Elpi.API.Utils.type_error
               "context entry applied to a non nominal")
      else None
  | _ -> None
let _ = elpi_is_ctx
let elpi_push_ctx ~depth:elpi__depth  elpi__state elpi__name elpi__ctx_item =
  let (elpi__ctx2dbl, elpi__dbl2ctx) =
    Elpi.API.State.get elpi_ctx_state elpi__state in
  let elpi__i = elpi__depth in
  let elpi__ctx2dbl = Elpi_ctx_Map.add elpi__name elpi__i elpi__ctx2dbl in
  let elpi__dbl2ctx =
    Elpi.API.RawData.Constants.Map.add elpi__i elpi__ctx_item elpi__dbl2ctx in
  let elpi__state =
    Elpi.API.State.set elpi_ctx_state elpi__state
      (elpi__ctx2dbl, elpi__dbl2ctx) in
  elpi__state
let _ = elpi_push_ctx
let elpi_pop_ctx ~depth:elpi__depth  elpi__state elpi__name =
  let (elpi__ctx2dbl, elpi__dbl2ctx) =
    Elpi.API.State.get elpi_ctx_state elpi__state in
  let elpi__i = elpi__depth in
  let elpi__ctx2dbl = Elpi_ctx_Map.remove elpi__name elpi__ctx2dbl in
  let elpi__dbl2ctx =
    Elpi.API.RawData.Constants.Map.remove elpi__i elpi__dbl2ctx in
  let elpi__state =
    Elpi.API.State.set elpi_ctx_state elpi__state
      (elpi__ctx2dbl, elpi__dbl2ctx) in
  elpi__state
let _ = elpi_pop_ctx
let rec elpi_embed_ctx :
  'elpi__param__poly_hyps .
    ((Elpi.API.RawData.constant * ctx), 'elpi__param__poly_hyps)
      Elpi.API.Conversion.embedding
  =
  fun ~depth:elpi__depth ->
    fun elpi__hyps ->
      fun elpi__constraints ->
        fun elpi__state ->
          function
          | (elpi__9, Entry (elpi__7, elpi__8)) ->
              let (elpi__state, elpi__13, elpi__10) =
                Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.embed
                  ~depth:elpi__depth elpi__hyps elpi__constraints elpi__state
                  elpi__9 in
              let (elpi__state, elpi__14, elpi__11) =
                Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                  elpi__constraints elpi__state elpi__7 in
              let (elpi__state, elpi__15, elpi__12) =
                Elpi.Builtin.PPX.embed_bool ~depth:elpi__depth elpi__hyps
                  elpi__constraints elpi__state elpi__8 in
              (elpi__state,
                (Elpi.API.RawData.mkAppL elpi_constant_constructor_ctx_Entryc
                   [elpi__13; elpi__14; elpi__15]),
                (List.concat [elpi__10; elpi__11; elpi__12]))
let _ = elpi_embed_ctx
let rec elpi_readback_ctx :
  'elpi__param__poly_hyps .
    ((Elpi.API.RawData.constant * ctx), 'elpi__param__poly_hyps)
      Elpi.API.Conversion.readback
  =
  fun ~depth:elpi__depth ->
    fun elpi__hyps ->
      fun elpi__constraints ->
        fun elpi__state ->
          fun elpi__x ->
            match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
            | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                elpi__hd == elpi_constant_constructor_ctx_Entryc ->
                let (elpi__state, elpi__6, elpi__5) =
                  Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.readback
                    ~depth:elpi__depth elpi__hyps elpi__constraints
                    elpi__state elpi__x in
                (match elpi__xs with
                 | elpi__1::elpi__2::[] ->
                     let (elpi__state, elpi__1, elpi__3) =
                       Elpi.API.PPX.readback_string ~depth:elpi__depth
                         elpi__hyps elpi__constraints elpi__state elpi__1 in
                     let (elpi__state, elpi__2, elpi__4) =
                       Elpi.Builtin.PPX.readback_bool ~depth:elpi__depth
                         elpi__hyps elpi__constraints elpi__state elpi__2 in
                     (elpi__state, (elpi__6, (Entry (elpi__1, elpi__2))),
                       (List.concat [elpi__5; elpi__3; elpi__4]))
                 | _ ->
                     Elpi.API.Utils.type_error
                       ("Not enough arguments to constructor: " ^
                          (Elpi.API.RawData.Constants.show
                             elpi_constant_constructor_ctx_Entryc)))
            | _ ->
                Elpi.API.Utils.type_error
                  (Format.asprintf "Not a constructor of type %s: %a" "ctx"
                     (Elpi.API.RawPp.term elpi__depth) elpi__x)
let _ = elpi_readback_ctx
let ctx :
  'elpi__param__poly_hyps .
    ((Elpi.API.RawData.constant * ctx),
      'elpi__param__poly_hyps as 'elpi__param__poly_hyps)
      Elpi.API.Conversion.t
  =
  let kind = Elpi.API.Conversion.TyName "ctx" in
  {
    Elpi.API.Conversion.ty = kind;
    pp_doc =
      (fun fmt ->
         fun () ->
           Elpi.API.PPX.Doc.kind fmt kind ~doc:"ctx";
           Elpi.API.PPX.Doc.constructor fmt
             ~ty:(Elpi.API.Conversion.TyName "prop") ~name:"entry"
             ~doc:"Entry"
             ~args:[Elpi.API.BuiltInData.nominal.Elpi.API.Conversion.ty;
                   Elpi.API.BuiltInData.string.Elpi.API.Conversion.ty;
                   Elpi.Builtin.bool.Elpi.API.Conversion.ty]);
    pp = (fun fmt -> fun (_, x) -> pp_ctx fmt x);
    embed = elpi_embed_ctx;
    readback = elpi_readback_ctx
  }
let _ = ctx
let in_ctx =
  {
    Elpi.API.Conversion.is_entry_for_nominal = elpi_is_ctx;
    to_key = elpi_ctx_to_key;
    push = elpi_push_ctx;
    pop = elpi_pop_ctx;
    conv = ctx;
    init =
      (fun state ->
         Elpi.API.State.set elpi_ctx_state state
           ((Elpi_ctx_Map.empty : Elpi.API.RawData.constant Elpi_ctx_Map.t),
             (Elpi.API.RawData.Constants.Map.empty : ctx
                                                       Elpi.API.Conversion.ctx_entry
                                                       Elpi.API.RawData.Constants.Map.t)));
    get = (fun state -> snd @@ (Elpi.API.State.get elpi_ctx_state state))
  }
let _ = in_ctx
let elpi_ctx = Elpi.API.BuiltIn.MLData ctx
let _ = elpi_ctx
let () = declaration := ((!declaration) @ [elpi_ctx])
[@@@end]

let ctx : 'c. (int * ctx, 'c) Elpi.API.Conversion.t  = ctx
let in_ctx : (ctx, string) Elpi.API.Conversion.context = in_ctx

let pp_term _ _ = ()
type term =
  | Var of string [@elpi.var ctx]
  | App of term * term
  | Lam of bool * string * (term[@elpi.binder "term" ctx (fun b s -> Entry(s,b))])
[@@deriving_inline elpi { declaration }]
let _ = fun (_ : term) -> ()
[@@@warning "-26-27-32-39-60"]
let elpi_constant_type_term = "term"
let _ = elpi_constant_type_term
let elpi_constant_type_termc =
  Elpi.API.RawData.Constants.declare_global_symbol elpi_constant_type_term
let _ = elpi_constant_type_termc
let elpi_constant_constructor_term_Var = "var"
let _ = elpi_constant_constructor_term_Var
let elpi_constant_constructor_term_Varc =
  Elpi.API.RawData.Constants.declare_global_symbol
    elpi_constant_constructor_term_Var
let _ = elpi_constant_constructor_term_Varc
let elpi_constant_constructor_term_App = "app"
let _ = elpi_constant_constructor_term_App
let elpi_constant_constructor_term_Appc =
  Elpi.API.RawData.Constants.declare_global_symbol
    elpi_constant_constructor_term_App
let _ = elpi_constant_constructor_term_Appc
let elpi_constant_constructor_term_Lam = "lam"
let _ = elpi_constant_constructor_term_Lam
let elpi_constant_constructor_term_Lamc =
  Elpi.API.RawData.Constants.declare_global_symbol
    elpi_constant_constructor_term_Lam
let _ = elpi_constant_constructor_term_Lamc
let rec elpi_embed_term :
  'elpi__param__poly_hyps .
    (term, 'elpi__param__poly_hyps) Elpi.API.Conversion.embedding
  =
  fun ~depth:elpi__depth ->
    fun elpi__hyps ->
      fun elpi__constraints ->
        fun elpi__state ->
          function
          | Var elpi__29 ->
              let (elpi__ctx2dbl, _) =
                Elpi.API.State.get elpi_ctx_state elpi__state in
              let elpi__key = (fun x -> x) elpi__29 in
              (if not (Elpi_ctx_Map.mem elpi__key elpi__ctx2dbl)
               then Elpi.API.Utils.error "Unbound variable";
               (elpi__state,
                 (Elpi.API.RawData.mkBound
                    (Elpi_ctx_Map.find elpi__key elpi__ctx2dbl)), []))
          | App (elpi__32, elpi__33) ->
              let (elpi__state, elpi__36, elpi__34) =
                elpi_embed_term ~depth:elpi__depth elpi__hyps
                  elpi__constraints elpi__state elpi__32 in
              let (elpi__state, elpi__37, elpi__35) =
                elpi_embed_term ~depth:elpi__depth elpi__hyps
                  elpi__constraints elpi__state elpi__33 in
              (elpi__state,
                (Elpi.API.RawData.mkAppL elpi_constant_constructor_term_Appc
                   [elpi__36; elpi__37]), (List.concat [elpi__34; elpi__35]))
          | Lam (elpi__38, elpi__39, elpi__40) ->
              let (elpi__state, elpi__44, elpi__41) =
                Elpi.Builtin.PPX.embed_bool ~depth:elpi__depth elpi__hyps
                  elpi__constraints elpi__state elpi__38 in
              let (elpi__state, elpi__45, elpi__42) =
                Elpi.API.PPX.embed_string ~depth:elpi__depth elpi__hyps
                  elpi__constraints elpi__state elpi__39 in
              let elpi__ctx_entry =
                (fun b -> fun s -> Entry (s, b)) elpi__38 elpi__39 in
              let elpi__ctx_key =
                elpi_ctx_to_key ~depth:elpi__depth elpi__ctx_entry in
              let elpi__ctx_entry =
                {
                  Elpi.API.Conversion.entry = elpi__ctx_entry;
                  depth = elpi__depth
                } in
              let elpi__state =
                elpi_push_ctx ~depth:(elpi__depth + 1) elpi__state
                  elpi__ctx_key elpi__ctx_entry in
              let (elpi__state, elpi__47, elpi__43) =
                elpi_embed_term ~depth:(elpi__depth + 1) elpi__hyps
                  elpi__constraints elpi__state elpi__40 in
              let elpi__46 = Elpi.API.RawData.mkLam elpi__47 in
              let elpi__state =
                elpi_pop_ctx ~depth:(elpi__depth + 1) elpi__state
                  elpi__ctx_key in
              (elpi__state,
                (Elpi.API.RawData.mkAppL elpi_constant_constructor_term_Lamc
                   [elpi__44; elpi__45; elpi__46]),
                (List.concat [elpi__41; elpi__42; elpi__43]))
let _ = elpi_embed_term
let rec elpi_readback_term :
  'elpi__param__poly_hyps .
    (term, 'elpi__param__poly_hyps) Elpi.API.Conversion.readback
  =
  fun ~depth:elpi__depth ->
    fun elpi__hyps ->
      fun elpi__constraints ->
        fun elpi__state ->
          fun elpi__x ->
            match Elpi.API.RawData.look ~depth:elpi__depth elpi__x with
            | Elpi.API.RawData.Const elpi__hd when elpi__hd >= 0 ->
                let (_, elpi__dbl2ctx) =
                  Elpi.API.State.get elpi_ctx_state elpi__state in
                (if
                   not
                     (Elpi.API.RawData.Constants.Map.mem elpi__hd
                        elpi__dbl2ctx)
                 then
                   Elpi.API.Utils.error
                     (Format.asprintf "Unbound variable: %s in %a"
                        (Elpi.API.RawData.Constants.show elpi__hd)
                        (Elpi.API.RawData.Constants.Map.pp
                           (Elpi.API.Conversion.pp_ctx_entry pp_ctx))
                        elpi__dbl2ctx);
                 (let { Elpi.API.Conversion.entry = elpi__entry;
                        depth = elpi__depth }
                    =
                    Elpi.API.RawData.Constants.Map.find elpi__hd
                      elpi__dbl2ctx in
                  (elpi__state,
                    (Var (elpi_ctx_to_key ~depth:elpi__depth elpi__entry)),
                    [])))
            | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                elpi__hd == elpi_constant_constructor_term_Appc ->
                let (elpi__state, elpi__22, elpi__21) =
                  elpi_readback_term ~depth:elpi__depth elpi__hyps
                    elpi__constraints elpi__state elpi__x in
                (match elpi__xs with
                 | elpi__19::[] ->
                     let (elpi__state, elpi__19, elpi__20) =
                       elpi_readback_term ~depth:elpi__depth elpi__hyps
                         elpi__constraints elpi__state elpi__19 in
                     (elpi__state, (App (elpi__22, elpi__19)),
                       (List.concat [elpi__21; elpi__20]))
                 | _ ->
                     Elpi.API.Utils.type_error
                       ("Not enough arguments to constructor: " ^
                          (Elpi.API.RawData.Constants.show
                             elpi_constant_constructor_term_Appc)))
            | Elpi.API.RawData.App (elpi__hd, elpi__x, elpi__xs) when
                elpi__hd == elpi_constant_constructor_term_Lamc ->
                let (elpi__state, elpi__28, elpi__27) =
                  Elpi.Builtin.PPX.readback_bool ~depth:elpi__depth
                    elpi__hyps elpi__constraints elpi__state elpi__x in
                (match elpi__xs with
                 | elpi__23::elpi__24::[] ->
                     let (elpi__state, elpi__23, elpi__25) =
                       Elpi.API.PPX.readback_string ~depth:elpi__depth
                         elpi__hyps elpi__constraints elpi__state elpi__23 in
                     let elpi__ctx_entry =
                       (fun b -> fun s -> Entry (s, b)) elpi__28 elpi__23 in
                     let elpi__ctx_key =
                       elpi_ctx_to_key ~depth:elpi__depth elpi__ctx_entry in
                     let elpi__ctx_entry =
                       {
                         Elpi.API.Conversion.entry = elpi__ctx_entry;
                         depth = elpi__depth
                       } in
                     let elpi__state =
                       elpi_push_ctx ~depth:elpi__depth elpi__state
                         elpi__ctx_key elpi__ctx_entry in
                     let (elpi__state, elpi__24, elpi__26) =
                       match Elpi.API.RawData.look ~depth:elpi__depth
                               elpi__24
                       with
                       | Elpi.API.RawData.Lam elpi__bo ->
                           elpi_readback_term ~depth:(elpi__depth + 1)
                             elpi__hyps elpi__constraints elpi__state
                             elpi__bo
                       | _ -> assert false in
                     let elpi__state =
                       elpi_pop_ctx ~depth:elpi__depth elpi__state
                         elpi__ctx_key in
                     (elpi__state, (Lam (elpi__28, elpi__23, elpi__24)),
                       (List.concat [elpi__27; elpi__25; elpi__26]))
                 | _ ->
                     Elpi.API.Utils.type_error
                       ("Not enough arguments to constructor: " ^
                          (Elpi.API.RawData.Constants.show
                             elpi_constant_constructor_term_Lamc)))
            | _ ->
                Elpi.API.Utils.type_error
                  (Format.asprintf "Not a constructor of type %s: %a" "term"
                     (Elpi.API.RawPp.term elpi__depth) elpi__x)
let _ = elpi_readback_term
class type term_ctx =
  object
    inherit Elpi.API.Conversion.ctx
    method  ctx : ctx Elpi.API.Conversion.ctx_field
  end
let term :
  'elpi__param__poly_hyps .
    (term, #term_ctx as 'elpi__param__poly_hyps) Elpi.API.Conversion.t
  =
  let kind = Elpi.API.Conversion.TyName "term" in
  {
    Elpi.API.Conversion.ty = kind;
    pp_doc =
      (fun fmt ->
         fun () ->
           Elpi.API.PPX.Doc.kind fmt kind ~doc:"term";
           Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"app" ~doc:"App"
             ~args:[Elpi.API.Conversion.TyName elpi_constant_type_term;
                   Elpi.API.Conversion.TyName elpi_constant_type_term];
           Elpi.API.PPX.Doc.constructor fmt ~ty:kind ~name:"lam" ~doc:"Lam"
             ~args:[Elpi.Builtin.bool.Elpi.API.Conversion.ty;
                   Elpi.API.BuiltInData.string.Elpi.API.Conversion.ty;
                   Elpi.API.Conversion.TyApp
                     ("->", (Elpi.API.Conversion.TyName "term"),
                       [Elpi.API.Conversion.TyName elpi_constant_type_term])]);
    pp = pp_term;
    embed = elpi_embed_term;
    readback = elpi_readback_term
  }
let _ = term
let elpi_term = Elpi.API.BuiltIn.MLData term
let _ = elpi_term
class term_ctx h  s =
  object (_)
    inherit  ((Elpi.API.Conversion.ctx) h)
    method ctx = in_ctx.Elpi.API.Conversion.get s
  end
let () = declaration := ((!declaration) @ [elpi_term])
[@@@end]

let term : 'c. (term, #term_ctx as 'c) Elpi.API.Conversion.t  = term
let in_term_ctx : term_ctx Elpi.API.Conversion.ctx_readback =
  fun ~depth h c s ->
    let s, gls = Elpi.API.PPX.readback_context [Elpi.API.PPX.C in_ctx] ~depth h c s in
    s, new term_ctx h s, gls

open Elpi.API
open BuiltInPredicate
open Notation

let term_to_string = Pred("term->string",
  In(term,"T",
  Out(BuiltInData.string,"S",
  Read("what else"))),in_term_ctx,
  fun (t : term) (_ety : string oarg)
    ~depth:_ c (_cst : Data.constraints) (_state : State.t) ->

    !: (Format.asprintf "@[<hov>%a@ |-@ %a@]@\n%!"
      (RawData.Constants.Map.pp (Conversion.pp_ctx_entry pp_ctx)) c#ctx
       term.pp t)

)

let builtin1 = let open BuiltIn in
  declare ~file_name:"test_ppx.elpi" (!declaration @ [
    MLCode(term_to_string,DocAbove);
    LPDoc "----------------- elpi ----------------"
  ] @ Elpi.Builtin.(core_builtins @ elpi_builtins))

let builtin2 = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !declaration

let main () =
  let _elpi, _ = Setup.init ~builtins:[builtin1;builtin2] ~basedir:"." [] in
  BuiltIn.document_file builtin1;
  exit 0
;;
