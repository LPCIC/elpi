(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_parser
open Elpi_runtime
open Elpi_compiler

module type Runtime = (module type of Runtime_trace_off)

let r = ref (module Runtime_trace_off : Runtime)

let set_runtime b =
  begin match b with
  | true  -> r := (module Runtime  : Runtime)
  | false -> r := (module Runtime_trace_off : Runtime)
  end;
  let module R = (val !r) in
  Util.set_spaghetti_printer Util.pp_const R.Pp.pp_constant

let set_trace argv =
  let args = Trace_ppx_runtime.Runtime.parse_argv argv in
  set_runtime !Trace_ppx_runtime.Runtime.debug;
  args

module Setup = struct

type state_descriptor = Data.State.descriptor
type quotations_descriptor = Compiler_data.QuotationHooks.descriptor ref
type hoas_descriptor = Data.HoasHooks.descriptor ref
type calc_descriptor = Data.CalcHooks.descriptor ref

let default_state_descriptor = Data.State.new_descriptor ()
let default_quotations_descriptor = Compiler_data.QuotationHooks.new_descriptor ()
let default_hoas_descriptor = Data.HoasHooks.new_descriptor ()
let default_calc_descriptor = Data.CalcHooks.new_descriptor ()

type builtins = Compiler.builtins
type elpi = {
  parser : (module Parse.Parser);
  resolver : ?cwd:string -> unit:string -> unit -> string;
  header : Compiler.header
}
type flags = Compiler.flags

let init ?(flags=Compiler.default_flags) ?(state=default_state_descriptor) ?(quotations=default_quotations_descriptor) ?(hoas=default_hoas_descriptor) ?(calc=default_calc_descriptor) ~builtins ?file_resolver () : elpi =
  (* At the moment we can only init the parser once *)
  let file_resolver =
    match file_resolver with
    | Some x -> x
    | None -> fun ?cwd:_ ~unit:_ () ->
        raise (Failure "'accumulate' is disabled since Setup.init was not given a ~file_resolver.") in
  let parser = (module Parse.Make(struct let resolver = file_resolver end) : Parse.Parser) in
  Data.Global_symbols.lock ();
  let header_src =
    builtins |> List.map (fun (fname,decls) ->
      (* This is a bit ugly, since we print and then parse... *)
      let b = Buffer.create 1024 in
      let fmt = Format.formatter_of_buffer b in
      Data.BuiltInPredicate.document fmt decls (List.rev !calc);
      Format.pp_print_flush fmt ();
      let text = Buffer.contents b in
      let lexbuf = Lexing.from_string text in
      let module P = (val parser) in
      try
        P.program_from ~loc:(Util.Loc.initial fname) lexbuf
      with Parse.ParseError(loc,msg) ->
        List.iteri (fun i s ->
          Printf.eprintf "%4d: %s\n" (i+1) s)
          (Re.Str.(split_delim (regexp_string "\n") text));
        begin try Printf.eprintf "Excerpt of %s:\n%s\n" fname
          (String.sub text loc.Util.Loc.line_starts_at
            Util.Loc.(loc.source_stop - loc.line_starts_at))
        with _ -> (* loc could be bogus *) (); end;
        Util.anomaly ~loc msg) in
  let header =
    try Compiler.header_of_ast ~flags ~parser state !quotations !hoas !calc builtins (List.concat header_src)
    with Compiler_data.CompileError(loc,msg) -> Util.anomaly ?loc msg in
  { parser; header; resolver = file_resolver }

let trace = set_trace

let usage =
  Trace_ppx_runtime.Runtime.usage

let set_warn = Util.set_warn
let set_error = Util.set_error
let set_anomaly = Util.set_anomaly
let set_type_error = Util.set_type_error
let set_std_formatter = Util.set_std_formatter
let set_err_formatter fmt =
  Util.set_err_formatter fmt; Trace_ppx_runtime.Runtime.(set_trace_output TTY fmt)

end

module EA = Ast

module Ast = struct
  type program = Ast.Program.t
  type query = Ast.Goal.t
  module Loc = Util.Loc
  module Goal = Ast.Goal
  module Scope = Compiler_data.Scope
  module Term = Compiler_data.ScopedTerm.QTerm
  module Type = Compiler_data.ScopedTypeExpression.SimpleType
  module Name = struct
    include Ast.Func
    type constant = int
    let is_global f i = show f = Util.Constants.Map.find i Data.Global_symbols.table.c2s
  end
  module Opaque = Util.CData
end

module Parse = struct

  let program ~elpi:{ Setup.parser } ~files =
    let module P = (val parser) in
    List.(concat (map (fun file -> P.program ~file) files))

  let program_from ~elpi:{ Setup.parser } ~loc buf =
    let module P = (val parser) in
    P.program_from ~loc buf

  let goal ~elpi:{ Setup.parser } ~loc ~text =
    let module P = (val parser) in
    P.goal ~loc ~text
  let goal_from ~elpi:{ Setup.parser } ~loc buf =
    let module P = (val parser) in
    P.goal_from ~loc buf

  exception ParseError = Elpi_parser.Parser_config.ParseError

  let resolve_file ~elpi:{ Setup.resolver } = resolver
  let std_resolver = Elpi_util.Util.std_resolver

end

module ED = Data

module Data = struct
  type term = Data.term
  type constraints = Data.constraints
  type state = Data.State.t
  type pretty_printer_context = ED.pp_ctx
  module StrMap = Util.StrMap
  type solution = {
    assignments : term StrMap.t;
    constraints : constraints;
    state : state;
    pp_ctx : pretty_printer_context;
    relocate_assignment_to_runtime : target:Compiler.program -> depth:int -> string -> (term, string) Stdlib.Result.t
  }
  type hyp = Data.clause_src = {
    hdepth : int;
    hsrc : term
  }
  type hyps = hyp list
end

module Compile = struct

  type program = Compiler.program
  type query = Compiler.query
  type executable = ED.executable
  type scoped_program = Compiler.scoped_program
  type compilation_unit = Compiler.checked_compilation_unit
  type compilation_unit_signature = Compiler.checked_compilation_unit_signature
  exception CompileError = Compiler_data.CompileError

  let to_setup_flags x = x

  let program ?(flags=Compiler.default_flags) ~elpi:{ Setup.header } l =
    Compiler.program_of_ast ~flags ~header (List.flatten l)

  let empty_base ~elpi:{ Setup.header } = Compiler.empty_base ~header

  let query s_p t =
    Compiler.query_of_ast s_p t (fun st -> st)

  let total_type_checking_time q = Compiler.total_type_checking_time q

  module StrSet = Util.StrSet

  type flags = Compiler.flags = {
    defined_variables : StrSet.t;
    print_units : bool;
  }
  let default_flags = Compiler.default_flags
  let optimize = Compiler.optimize_query
  let scope ?(flags=Compiler.default_flags) ~elpi:{ Setup.header } a =
    Compiler.scoped_of_ast ~flags ~header a
  let unit ?(flags=Compiler.default_flags) ~elpi:{ Setup.header } ~base ?builtins x =
    Compiler.unit_of_scoped ~flags ~header ?builtins x |> Compiler.check_unit ~base

  let extend ?(flags=Compiler.default_flags) ~base u = Compiler.append_unit ~flags ~base u
  let signature u = Compiler.signature_of_checked_compilation_unit u
  let extend_signature ?(flags=Compiler.default_flags) ~base u = Compiler.append_unit_signature ~flags ~base u

end

module Execute = struct
  type outcome =
    Success of Data.solution | Failure | NoMoreSteps

  let rec uvar2discard ~depth t =
    let open ED in
    let module R = (val !r) in
    match R.deref_head ~depth t with
    | App(c,x,xs) -> mkApp c (uvar2discard ~depth x) (List.map (uvar2discard ~depth) xs)
    | Cons(x,xs) -> mkCons (uvar2discard ~depth x) (uvar2discard ~depth xs)
    | Lam x -> mkLam (uvar2discard ~depth:(depth+1) x)
    | Builtin(c,xs) -> mkBuiltin c (List.map (uvar2discard ~depth) xs)
    | UVar _ | AppUVar _ -> mkDiscard
    | Arg _ | AppArg _ -> assert false
    | Const _ | Nil | CData _ | Discard -> t
  
  let map_outcome full_deref hmove = function
    | ED.Failure -> Failure
    | ED.NoMoreSteps -> NoMoreSteps
    | ED.Success { ED.assignments; constraints; state; pp_ctx; state_for_relocation = (idepth,from); } -> 
      Success { assignments; constraints; state; pp_ctx;
        relocate_assignment_to_runtime = (fun ~target ~depth s ->
          Compiler.relocate_closed_term ~from
            (Util.StrMap.find s assignments |> full_deref ~depth:idepth |> uvar2discard ~depth:idepth) ~to_:target
          |> Stdlib.Result.map (hmove ?avoid:None ~from:depth ~to_:depth)
        );
        }

  let once ?max_steps ?delay_outside_fragment p =
    let module R = (val !r) in
    map_outcome R.full_deref R.hmove @@ R.execute_once ?max_steps ?delay_outside_fragment p
  let loop ?delay_outside_fragment p ~more ~pp =
    let module R = (val !r) in
    R.execute_loop ?delay_outside_fragment p ~more ~pp:(fun t o -> pp t (map_outcome R.full_deref R.hmove o))

end

module Pp = struct
  let term pp_ctx f t = (* XXX query depth *)
    let module R = (val !r) in let open R in
    Pp.uppterm ~pp_ctx 0 [] ~argsdepth:0 [||] f t

  let constraints pp_ctx f c =
    let module R = (val !r) in let open R in
    Util.pplist ~boxed:true (pp_stuck_goal ~pp_ctx) "" f c

  let state = ED.State.pp

  let program f c =
    let module R = (val !r) in let open R in
    Compiler.pp_program (fun ~pp_ctx ~depth -> Pp.uppterm ~pp_ctx depth [] ~argsdepth:0 [||]) f c
  let goal f c =
    let module R = (val !r) in let open R in
    Compiler.pp_goal (fun ~pp_ctx ~depth -> Pp.uppterm ~pp_ctx depth [] ~argsdepth:0 [||]) f c
  
  module Ast = struct
    let program = EA.Program.pp
    let query = EA.Goal.pp
  end
end

(****************************************************************************)

module Conversion = struct
type ty_ast = ED.Conversion.ty_ast = TyName of string | TyApp of string * ty_ast * ty_ast list

type extra_goal = ED.Conversion.extra_goal = ..
type extra_goal +=
  | Unify = ED.Conversion.Unify

type extra_goals = extra_goal list

type 'a embedding = 'a ED.Conversion.embedding

type 'a readback = 'a ED.Conversion.readback

type 'a t = 'a ED.Conversion.t =  {
  ty : ty_ast;
  pp_doc : Format.formatter -> unit -> unit;
  pp : Format.formatter -> 'a -> unit;
  embed : 'a embedding;   (* 'a -> term *)
  readback : 'a readback; (* term -> 'a *)
}

exception TypeErr = ED.Conversion.TypeErr

end

module ContextualConversion = ED.ContextualConversion

module RawOpaqueData = struct

  type name = string
  type doc = string

  type 'a declaration = {
    name : name;
    doc : doc;
    pp : Format.formatter -> 'a -> unit;
    compare : 'a -> 'a -> int;
    hash : 'a -> int;
    hconsed : bool;
    constants : (name * 'a) list; (* global constants of that type, eg "std_in" *)
  }
  type t = Util.CData.t
  type 'a cdata = {
    cin : 'a -> Data.term;
    cino : 'a -> Ast.Opaque.t;
    isc : t -> bool;
    cout: t -> 'a;
    name : string;
  }
  let conversion_of_cdata ~name ?(doc="") ~constants_map ~values_map ~constants
     ~pp ({ Util.CData.cin; isc; cout; name = c } )
  =
  let ty = Conversion.TyName name in
  let cino x = cin x in
  let cin x =
    let module R = (val !r) in
    try R.mkConst (values_map x)
    with Not_found -> ED.Term.CData (cin x) in
  let embed ~depth:_ state x =
    state, cin x, [] in
  let readback ~depth state t =
    let module R = (val !r) in let open R in
    match deref_head ~depth t with
    | ED.Term.CData c when isc c -> state, cout c, []
    | ED.Term.Const i as t when i < 0 ->
        begin try state, Util.Constants.Map.find i constants_map, []
        with Not_found -> raise (Conversion.TypeErr(ty,depth,t)) end
    | t -> raise (Conversion.TypeErr(ty,depth,t)) in
  let pp_doc fmt () =
    if doc <> "" then begin
      ED.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
      Format.fprintf fmt "@\n";
    end;
    Format.fprintf fmt "@[<hov 2>kind %s type.@]@\n@\n" name;
    List.iter (fun (c,_) ->
      Format.fprintf fmt "@[<hov 2>type %s %s.@]@\n" c name)
      constants
    in
  { cin; cino; cout; isc; name = c },
  { Conversion.embed; readback; ty; pp_doc; pp }

  let conversion_of_cdata (type a) ~name ?doc ?(constants=[]) ~compare ~pp cd =
    let module VM = Map.Make(struct type t = a let compare = compare end) in
    let constants_map, values_map =
      List.fold_right (fun (n,v) (cm,vm) ->
        let c = ED.Global_symbols.declare_global_symbol n in
        Util.Constants.Map.add c v cm, VM.add v c vm)
      constants (Util.Constants.Map.empty,VM.empty) in
    let values_map x = VM.find x values_map in
    conversion_of_cdata ~name ?doc ~constants_map ~values_map ~constants ~pp cd

  let declare { name; doc; pp; compare; hash; hconsed; constants; } =
    let cdata = Util.CData.declare {
      data_compare = compare;
      data_pp = pp;
      data_hash = hash;
      data_name = name;
      data_hconsed = hconsed;
   } in
   conversion_of_cdata ~name ~doc ~constants ~compare ~pp cdata

   let morph1 { cin; cout } f x = cin (f (cout x))
   let morph2 { cin; cout } f x y = cin (f (cout x) (cout y))
   let map { cout } { cin } f x = cin (f (cout x))
   let ty2 { isc } x y = isc x && isc y

   let hcons = Util.CData.hcons
   let name = Util.CData.name
   let hash = Util.CData.hash
   let compare = Util.CData.compare
   let show = Util.CData.show
   let pp = Util.CData.pp
   let equal = Util.CData.equal

   let int =
     let { Util.CData.cin; cout; isc; name } = ED.C.int in
     { cin = (fun x -> ED.mkCData (cin x)); cino = cin; cout; isc; name }
   let is_int = ED.C.is_int
   let to_int = ED.C.to_int
   let of_int = ED.C.of_int
   let float =
     let { Util.CData.cin; cout; isc; name } = ED.C.float in
     { cin = (fun x -> ED.mkCData (cin x)); cino = cin; cout; isc; name }
   let is_float = ED.C.is_float
   let to_float = ED.C.to_float
   let of_float = ED.C.of_float
   let string =
     let { Util.CData.cin; cout; isc; name } = ED.C.string in
     { cin = (fun x -> ED.mkCData (cin x)); cino = cin; cout; isc; name }
   let is_string = ED.C.is_string
   let to_string = ED.C.to_string
   let of_string = ED.C.of_string
   let loc =
     let { Util.CData.cin; cout; isc; name } = ED.C.loc in
     { cin = (fun x -> ED.mkCData (cin x)); cino = cin; cout; isc; name }
   let is_loc = ED.C.is_loc
   let to_loc = ED.C.to_loc
   let of_loc = ED.C.of_loc

end


module OpaqueData = struct

  type name = string
  type doc = string

  type 'a declaration = 'a RawOpaqueData.declaration = {
    name : name;
    doc : doc;
    pp : Format.formatter -> 'a -> unit;
    compare : 'a -> 'a -> int;
    hash : 'a -> int;
    hconsed : bool;
    constants : (name * 'a) list; (* global constants of that type, eg "std_in" *)
  }

  let declare x = snd @@ RawOpaqueData.declare x

end

module BuiltInData = struct

  let int    = snd @@ RawOpaqueData.conversion_of_cdata ~name:"int"    ~compare:(fun x y -> x - y) ~pp:(fun fmt x -> Util.CData.pp fmt (ED.C.int.Util.CData.cin x)) ED.C.int
  let float  = snd @@ RawOpaqueData.conversion_of_cdata ~name:"float"  ~compare:Float.compare      ~pp:(fun fmt x -> Util.CData.pp fmt (ED.C.float.Util.CData.cin x)) ED.C.float
  let string = snd @@ RawOpaqueData.conversion_of_cdata ~name:"string" ~compare:String.compare     ~pp:(fun fmt x -> Util.CData.pp fmt (ED.C.string.Util.CData.cin x)) ED.C.string
  let loc    = snd @@ RawOpaqueData.conversion_of_cdata ~name:"loc"    ~compare:Util.Loc.compare   ~pp:(fun fmt x -> Util.CData.pp fmt (ED.C.loc.Util.CData.cin x)) ED.C.loc
  let poly ty =
    let embed ~depth:_ state x = state, x, [] in
    let readback ~depth state t = state, t, [] in
    { Conversion.embed; readback; ty = Conversion.TyName ty;
      pp = (fun fmt _ -> Format.fprintf fmt "<poly>");
      pp_doc = (fun fmt () -> ()) }

  let any = poly "any"

  let fresh_copy t depth =
    let module R = (val !r) in let open R in
    let open ED in
    let rec aux d t =
      match deref_head ~depth:(depth + d) t with
      | Lam t -> mkLam (aux (d+1) t)
      | Const c as x ->
          if c < 0 || c >= depth then x
          else raise Conversion.(TypeErr(TyName"closed term",depth+d,x))
      | App (c,x,xs) ->
          if c < 0 || c >= depth then mkApp c (aux d x) (List.map (aux d) xs)
          else raise Conversion.(TypeErr(TyName"closed term",depth+d,x))
      | (UVar _ | AppUVar _) as x ->
          raise Conversion.(TypeErr(TyName"closed term",depth+d,x))
      | Arg _ | AppArg _ -> assert false
      | Builtin (c,xs) -> mkBuiltin c (List.map (aux d) xs)
      | CData _ as x -> x
      | Cons (hd,tl) -> mkCons (aux d hd) (aux d tl)
      | Nil as x -> x
      | Discard as x -> x
    in
      (aux 0 t, depth)

  let closed ty =
    let ty = Conversion.(TyName ty) in
    let embed ~depth state (x,from) =
      let module R = (val !r) in let open R in
      state, hmove ~from ~to_:depth ?avoid:None x, [] in
    let readback ~depth state t =
      state, fresh_copy t depth, [] in
    { Conversion.embed; readback; ty;
      pp = (fun fmt (t,d) ->
        let module R = (val !r) in let open R in
        Pp.uppterm d [] ~argsdepth:d ED.empty_env fmt t);
      pp_doc = (fun fmt () -> ()) }
   
  let map_acc f s l =
    let rec aux acc extra s = function
    | [] -> s, List.rev acc, List.(concat (rev extra))
    | x :: xs ->
        let s, x, gls = f s x in
        aux (x :: acc) (gls :: extra) s xs
    in
      aux [] [] s l

  let listC d =
    let embed ~depth h c s l =
      let module R = (val !r) in let open R in
      let s, l, eg = map_acc (d.ContextualConversion.embed ~depth h c) s l in
      s, list_to_lp_list l, eg in
    let readback ~depth h c s t =
      let module R = (val !r) in let open R in
      map_acc (d.ContextualConversion.readback ~depth h c) s
        (lp_list_to_list ~depth t)
    in
    let pp fmt l =
      Format.fprintf fmt "[%a]" (Util.pplist d.pp ~boxed:true "; ") l in
    { ContextualConversion.embed; readback;
      ty = TyApp ("list",d.ty,[]);
      pp;
      pp_doc = (fun fmt () -> ()) }
  
  let list d =
    let embed ~depth s l =
      let module R = (val !r) in let open R in
      let s, l, eg = map_acc (d.Conversion.embed ~depth) s l in
      s, list_to_lp_list l, eg in
    let readback ~depth s t =
      let module R = (val !r) in let open R in
      map_acc (d.Conversion.readback ~depth) s
        (lp_list_to_list ~depth t)
    in
    let pp fmt l =
      Format.fprintf fmt "[%a]" (Util.pplist d.pp ~boxed:true "; ") l in
    { Conversion.embed; readback;
      ty = TyApp ("list",d.ty,[]);
      pp;
      pp_doc = (fun fmt () -> ()) }

end

module Elpi = struct

  type t = ED.uvar_body

  let pp = Compiler.pp
  let show m = Format.asprintf "%a" pp m

  let equal h1 h2  = h1 == h2
  let hash = ED.uvar_id 

  let fresh_name =
    let i = ref 0 in
    fun () -> incr i; Printf.sprintf "_uvk_%d_" !i
  let fresh () = Ast.Name.from_string @@ fresh_name ()

  let alloc_Elpi name state =
    let module R = (val !r) in
    state, (ED.oref ED.dummy)

  let make ?name state =
    match name with
    | None -> alloc_Elpi (fresh_name ()) state
    | Some name ->
        try state, Util.StrMap.find name (ED.State.get Compiler.uvk state)
        with Not_found ->
          let state, k = alloc_Elpi name state in
          ED.State.update Compiler.uvk state (Util.StrMap.add name k), k
    
  let get ~name state =
    try Some (Util.StrMap.find name (ED.State.get Compiler.uvk state))
    with Not_found -> None

end

module RawData = struct

  type constant = Util.constant
  type builtin = Util.constant
  type term = ED.Term.term
  type view =
    (* Pure subterms *)
    | Const of constant                   (* global constant or a bound var *)
    | Lam of term                         (* lambda abstraction, i.e. x\ *)
    | App of constant * term * term list  (* application (at least 1 arg) *)
    (* Optimizations *)
    | Cons of term * term                 (* :: *)
    | Nil                                 (* [] *)
    (* FFI *)
    | Builtin of builtin * term list      (* call to a built-in predicate *)
    | CData of RawOpaqueData.t                    (* external data *)
    (* Unassigned unification variables *)
    | UnifVar of Elpi.t * term list
  [@@warning "-37"]
  
  let rec look ~depth t =
    let module R = (val !r) in let open R in
    match deref_head ~depth t with
    | ED.Term.Arg _ | ED.Term.AppArg _ -> assert false
    | ED.Term.AppUVar(ub,0,args) -> UnifVar (ub,args)
    | ED.Term.AppUVar(ub,lvl,args) -> look ~depth (R.expand_appuv ub ~depth ~lvl ~args)
    | ED.Term.UVar(ub,lvl,ano) -> look ~depth (R.expand_uv ub ~depth ~lvl ~ano)
    | ED.Term.Discard ->
        let ub = ED.oref ED.dummy in
        UnifVar (ub,R.mkinterval 0 depth 0)
    | ED.Term.Lam _ as t ->
        begin match R.eta_contract_flex ~depth t with
        | None -> Obj.magic t (* HACK: view is a "subtype" of Term.term *)
        | Some t -> look ~depth t
        end
    | x -> Obj.magic x (* HACK: view is a "subtype" of Term.term *)

  let kool = function
    | UnifVar(ub,args) -> ED.Term.AppUVar(ub,0,args)
    | x -> Obj.magic x
  [@@ inline]

  let mkConst n = let module R = (val !r) in R.mkConst n
  let mkLam = ED.Term.mkLam
  let mkApp = ED.Term.mkApp
  let mkAppGlobal i x xs =
    if i >= 0 then Util.anomaly "mkAppGlobal: got a bound variable";
    ED.Term.mkApp i x xs
  let mkAppBound i x xs=
    if i < 0 then Util.anomaly "mkAppBound: got a global constant";
    ED.Term.mkApp i x xs
  let mkCons = ED.Term.mkCons
  let mkNil = ED.Term.mkNil
  let mkDiscard = ED.Term.mkDiscard
  let mkBuiltin = ED.Term.mkBuiltin
  let mkCData = ED.Term.mkCData
  let mkAppBoundL x l =
    if x < 0 then Util.anomaly "mkAppBoundL: got a global constant";
    let module R = (val !r) in R.mkAppL x l
  let mkAppGlobalL x l =
    if x >= 0 then Util.anomaly "mkAppBoundL: got a bound variable";
    let module R = (val !r) in R.mkAppL x l

  let mkGlobal i =
    if i >= 0 then Util.anomaly "mkGlobal: got a bound variable";
    mkConst i
  let mkBound i =
    if i < 0 then Util.anomaly "mkBound: got a global constant";
    mkConst i

  let cmp_builtin i j = i - j

  let mkAppMoreArgs ~depth hd args =
    let module R = (val !r) in let open R in
    match deref_head ~depth hd, args with
    | Const c, [] -> hd
    | Const c, x :: xs -> mkApp c x xs
    | App(c,x,xs), _ -> mkApp c x (xs@args)
    | Arg _, [] -> hd
    | Arg(i,ano), xs -> AppArg(i, mkinterval 0 ano 0 @ xs)
    | AppArg(i,args), xs -> AppArg(i,args @ xs)
    | _ -> assert false

  let isApp ~depth hd =
    let module R = (val !r) in let open R in
    match deref_head ~depth hd with
    | App _ -> true
    | _ -> false

  module Constants = struct

    let declare_global_symbol = ED.Global_symbols.declare_global_symbol

    let show c = Util.Constants.show c

    let eqc    = ED.Global_symbols.eqc
    let orc    = ED.Global_symbols.orc
    let andc   = ED.Global_symbols.andc
    let rimplc = ED.Global_symbols.rimplc
    let pic    = ED.Global_symbols.pic
    let sigmac = ED.Global_symbols.sigmac
    let implc  = ED.Global_symbols.implc
    let cutc   = ED.Global_symbols.cutc
    let ctypec = ED.Global_symbols.ctypec
    let spillc = ED.Global_symbols.spillc

    module Map = Util.Constants.Map
    module Set = Util.Constants.Set

  end

  let of_term x = x

  let of_hyp x = x
  let of_hyps x = x

  type hyp = Data.hyp = {
    hdepth : int;
    hsrc : term
  }
  type hyps = hyp list

  type suspended_goal = ED.suspended_goal = {
    context : hyps;
    goal : int * term
  }

  let constraints l =
    let module R = (val !r) in let open R in
    Util.map_filter (fun x -> get_suspended_goal x.ED.kind) l
  let no_constraints = []

  let mkUnifVar ub ~args state =
    ED.Term.mkAppUVar ub 0 args

  type Conversion.extra_goal +=
  | RawGoal = ED.Conversion.RawGoal

  let set_extra_goals_postprocessing ?(descriptor=Setup.default_hoas_descriptor) x =
    ED.HoasHooks.set_extra_goals_postprocessing ~descriptor x

  let new_hoas_descriptor = ED.HoasHooks.new_descriptor

end

module FlexibleData = struct

  module Elpi = Elpi

  module type Host = sig
    type t
    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
    val show : t -> string
  end

    (* Bijective map between elpi UVar and host equivalent *)
  let uvmap_no = ref 0
  module Map = functor(T : Host) -> struct
    open Util

    module H2E = Map.Make(T)

    type t = {
        h2e : Elpi.t H2E.t;
        e2h : T.t IntMap.t
    }

    let empty = {
      h2e = H2E.empty;
      e2h = IntMap.empty
    }

    let add uv v { h2e; e2h } =
      let h2e = H2E.add v uv h2e in
      { h2e; e2h = IntMap.add (ED.uvar_id uv) v e2h }

    let elpi v { h2e } = H2E.find v h2e
    let host ub { e2h } =
      IntMap.find (ED.uvar_id ub) e2h

    let remove_both ub v { h2e; e2h } = 
      let h2e = H2E.remove v h2e in
      { h2e; e2h = IntMap.remove (ED.uvar_id ub) e2h }

    let remove_elpi k m =
      let v = host k m in
      remove_both k v m

    let remove_host v m =
      let handle = elpi v m in
      remove_both handle v m

    let filter f { h2e; e2h } =
      let e2h = IntMap.filter (fun ub v -> f v (H2E.find v h2e)) e2h in
      let h2e = H2E.filter f h2e in
      { h2e; e2h }

    let fold f { h2e } acc =
      let module R = (val !r) in let open R in
      let get_val { ED.Term.contents = ub } =
         if ub != ED.dummy then Some (deref_head ~depth:0 ub)
         else None
      in
      H2E.fold (fun k uk acc -> f k uk (get_val uk) acc) h2e acc

    let uvn = incr uvmap_no; !uvmap_no

    let pp fmt (m : t) =
      let pp k uv _ () =
           Format.fprintf fmt "@[<h>%a@ <-> %a@]@ " T.pp k Elpi.pp uv
        in
      Format.fprintf fmt "@[<v>";
      fold pp m ();
      Format.fprintf fmt "@]"
    ;;

    let show m = Format.asprintf "%a" pp m

    let uvmap =
      ED.State.declare
      ~descriptor:ED.elpi_state_descriptor
      ~name:(Printf.sprintf "elpi:uvm:%d" uvn) ~pp
      ~clause_compilation_is_over:(fun x -> empty)
      ~compilation_is_over:(fun x -> Some x)
      ~execution_is_over:(fun x -> Some x)
      ~init:(fun () -> empty)
      ()

  end

  module type Show = Util.Show
  let uvar  = {
    Conversion.ty = Conversion.TyName "uvar";
    pp_doc = (fun fmt () -> Format.fprintf fmt "Unification variable, as the uvar keyword");
    pp = (fun fmt (k,_) -> Format.fprintf fmt "%a" Elpi.pp k);
    embed = (fun ~depth s (k,args) -> s, RawData.mkUnifVar k ~args s, []);
    readback = (fun ~depth state t ->
      match RawData.look ~depth t with
      | RawData.UnifVar(k,args) ->
          state, (k,args), []
      | _ -> raise (Conversion.TypeErr (TyName "uvar",depth,t)));
  }

end

module AlgebraicData = struct
  include ED.BuiltInPredicate.ADT
  type name = string
  type doc = string

  let declare x =
    let module R = (val !r) in
    ED.BuiltInPredicate.ADT.adt
      ~look:R.deref_head
      ~mkinterval:R.mkinterval
      ~mkConst:R.mkConst
      ~alloc:FlexibleData.Elpi.make
      ~mkUnifVar:RawData.mkUnifVar x
end

module BuiltInPredicate = struct
  type once = depth:int -> Data.term -> Data.state -> Data.state

  include ED.BuiltInPredicate
  exception No_clause = ED.No_clause

  let mkData x = Data x

  let ioargC a = let open ContextualConversion in { a with
    pp = (fun fmt -> function Data x -> a.pp fmt x | NoData -> Format.fprintf fmt "_");
    embed = (fun ~depth hyps csts state -> function
             | Data x -> a.embed ~depth hyps csts state x
             | NoData -> assert false);
    readback = (fun ~depth hyps csts state t ->
             let module R = (val !r) in let open R in
             let rec aux t =
               match deref_head ~depth t with
               | ED.Term.Arg _ | ED.Term.AppArg _ -> assert false
               | ED.Term.UVar _ | ED.Term.AppUVar _
               | ED.Term.Discard -> state, NoData, []
               | ED.Term.Lam _ ->
                   begin match R.eta_contract_flex ~depth t with
                   | None -> state, NoData, []
                   | Some t -> aux t
                   end
               | _ -> let state, x, gls = a.readback ~depth hyps csts state t in
                       state, mkData x, gls
             in
               aux t);
  }
  let ioarg a =
    let open ContextualConversion in
    !< (ioargC (!> a))

  let ioargC_flex a = let open ContextualConversion in { a with
    pp = (fun fmt -> function Data x -> a.pp fmt x | NoData -> Format.fprintf fmt "_");
    embed = (fun ~depth hyps csts state -> function
             | Data x -> a.embed ~depth hyps csts state x
             | NoData -> assert false);
    readback = (fun ~depth hyps csts state t ->
             let module R = (val !r) in let open R in
             match deref_head ~depth t with
             | ED.Term.Arg _ | ED.Term.AppArg _ -> assert false
             | ED.Term.Discard -> state, NoData, []
             | _ -> let state, x, gls = a.readback ~depth hyps csts state t in
                    state, mkData x, gls);
  }

  let ioarg_flex a =
    let open ContextualConversion in
    !< (ioargC_flex (!> a))

  let ioarg_any = let open Conversion in { BuiltInData.any with
    pp = (fun fmt -> function
             | Data x -> BuiltInData.any.pp fmt x
             | NoData -> Format.fprintf fmt "_");
    embed = (fun ~depth state -> function
             | Data x -> state, x, []
             | NoData -> assert false);
    readback = (fun ~depth state t ->
             let module R = (val !r) in
             match R.deref_head ~depth t with
             | ED.Term.Discard -> state, NoData, []
             | _ -> state, Data t, []);
  }

  module Notation = struct

    let (!:) x = (), Some x
    let (+!) a b = a, Some b
    let (?:) x = (), x
    let (+?) a b = a, b

  end

  let beta ~depth t args =
    let module R = (val !r) in let open R in
    deref_appuv ~from:depth ~to_:depth ?avoid:None args t

  module HOAdaptors = struct

    type 'a pred1 = Data.term * 'a Conversion.t
    type ('a,'b) pred2 = Data.term * 'a Conversion.t * 'b Conversion.t
    type ('a) pred2a = Data.term * 'a Conversion.t
    type ('a,'b,'c) pred3 = Data.term * 'a Conversion.t * 'b Conversion.t * 'c Conversion.t
    type ('a,'b) pred3a = Data.term * 'a Conversion.t * 'b Conversion.t

    let pred1_ty x = Conversion.TyApp("->",x.Conversion.ty,[Conversion.TyName"prop"])
    let pred1 x = { Conversion.ty = pred1_ty x; readback = (fun ~depth state e -> state,(e,x),[]); embed = (fun ~depth state (x,_) -> state,x,[]); pp = (fun fmt (x,_) -> Format.fprintf fmt "<pred1>"); pp_doc = (fun fmt () -> ()) }
    let pred2_ty x y = Conversion.(TyApp("->",x.Conversion.ty,[TyApp("->",y.Conversion.ty,[Conversion.TyName"prop"])]))
    let pred2 x y = { Conversion.ty = pred2_ty x y; readback = (fun ~depth state e -> state,(e,x,y),[]); embed = (fun ~depth state (x,_,_) -> state,x,[]); pp = (fun fmt (x,_,_) -> Format.fprintf fmt "<pred2>"); pp_doc = (fun fmt () -> ()) }
    let pred3_ty x y z = Conversion.(TyApp("->",x.Conversion.ty,[TyApp("->",y.Conversion.ty,[TyApp("->",z.Conversion.ty,[Conversion.TyName"prop"])])]))
    let pred3 x y z = { Conversion.ty = pred3_ty x y z; readback = (fun ~depth state e -> state,(e,x,y,z),[]); embed = (fun ~depth state (x,_,_,_) -> state,x,[]); pp = (fun fmt (x,_,_,_) -> Format.fprintf fmt "<pred3>"); pp_doc = (fun fmt () -> ()) }
    let pred2a_ty x a = Conversion.(TyApp("->",x.Conversion.ty,[TyApp("->",Conversion.TyName a,[TyApp("->",Conversion.TyName a,[Conversion.TyName"prop"])])]))
    let pred2a x a = { Conversion.ty = pred2a_ty x a; readback = (fun ~depth state e -> state,(e,x),[]); embed = (fun ~depth state (x,_) -> state,x,[]); pp = (fun fmt (x,_) -> Format.fprintf fmt "<pred2a>"); pp_doc = (fun fmt () -> ()) }
    let pred3a_ty x y a = Conversion.(TyApp("->",x.Conversion.ty,[TyApp("->",y.Conversion.ty,[TyApp("->",Conversion.TyName a,[TyApp("->",Conversion.TyName a,[Conversion.TyName"prop"])])])]))
    let pred3a x y a = { Conversion.ty = pred3a_ty x y a; readback = (fun ~depth state e -> state,(e,x,y),[]); embed = (fun ~depth state (x,_,_) -> state,x,[]); pp = (fun fmt (x,_,_) -> Format.fprintf fmt "<pred3a>"); pp_doc = (fun fmt () -> ()) }


    let filter1 ~once ~depth ~filter (f,c1) m state =
      let gls = ref [] in
      let st = ref state in
      let m = filter (fun x ->
        try
          let state, x, gls0 = c1.Conversion.embed ~depth !st x in
          if gls0 <> [] then gls := gls0 :: !gls;
          let state = once ~depth (beta ~depth f [x]) state in
          st := state;
          true
        with No_clause -> false) m in
      !st, m, List.concat @@ List.rev !gls
    let filter2 ~once ~depth ~filter (f,c1,c2) m state =
      let gls = ref [] in
      let st = ref state in
      let m = filter (fun x y ->
        try
          let state, x, gls0 = c1.Conversion.embed ~depth !st x in
          let state, y, gls1 = c2.Conversion.embed ~depth state y in
          if gls0 <> [] || gls1 <> [] then gls := gls1 :: gls0 :: !gls;
          let state = once ~depth (beta ~depth f [x;y]) state in
          st := state;
          true
        with No_clause -> false) m in
      !st, m, List.concat @@ List.rev !gls

    let map1 ~once ~depth ~map (f,c1,c2) m state =
      let gls = ref [] in
      let st = ref state in
      let m = map (fun x ->
          let state, x, gls0 = c1.Conversion.embed ~depth !st x in
          let state, y = FlexibleData.Elpi.make state in
          let y = RawData.mkUnifVar y ~args:(List.init depth RawData.mkConst) state in
          let state = once ~depth (beta ~depth f [x;y]) state in
          let state, y, gls1 = c2.Conversion.readback ~depth state y in
          if gls0 <> [] || gls1 <> [] then gls := gls1 :: gls0 :: !gls;
          st := state;
          y
        ) m in
      !st, m, List.concat @@ List.rev !gls

    let map2 ~once ~depth ~map (f,c1,c2,c3) m state =
      let gls = ref [] in
      let st = ref state in
      let m = map (fun x y ->
          let state, x, gls0 = c1.Conversion.embed ~depth !st x in
          let state, y, gls1 = c2.Conversion.embed ~depth state y in
          let state, z = FlexibleData.Elpi.make state in
          let z = RawData.mkUnifVar z ~args:(List.init depth RawData.mkConst) state in
          let state = once ~depth (beta ~depth f [x;y;z]) state in
          let state, z, gls2 = c3.Conversion.readback ~depth state z in
          if gls0 <> [] || gls1 <> [] || gls2 <> [] then gls := gls2 :: gls1 :: gls0 :: !gls;
          st := state;
          z
        ) m in
      !st, m, List.concat @@ List.rev !gls            

      let fold1 ~once ~depth ~fold (f,c1) m a state =
        let gls = ref [] in
        let st = ref state in
        let a = fold (fun x a ->
            let state, x, gls0 = c1.Conversion.embed ~depth !st x in
            let state, y = FlexibleData.Elpi.make state in
            let y = RawData.mkUnifVar y ~args:(List.init depth RawData.mkConst) state in
            if gls0 <> [] then gls := gls0 :: !gls;
            let state = once ~depth (beta ~depth f [x;a;y]) state in
            st := state;
            y
          ) m a in
        !st, a, List.concat @@ List.rev !gls
  
      let fold2 ~once ~depth ~fold (f,c1,c2) m a state =
        let gls = ref [] in
        let st = ref state in
        let a = fold (fun x y a ->
            let state, x, gls0 = c1.Conversion.embed ~depth !st x in
            let state, y, gls1 = c2.Conversion.embed ~depth state y in
            let state, z = FlexibleData.Elpi.make state in
            let z = RawData.mkUnifVar z ~args:(List.init depth RawData.mkConst) state in
            let state = once ~depth (beta ~depth f [x;y;a;z]) state in
            if gls0 <> [] || gls1 <> [] then gls := gls1 :: gls0 :: !gls;
            st := state;
            z
          ) m a in
        !st, a, List.concat @@ List.rev !gls            
        

  end

end

module BuiltIn = struct
  include ED.BuiltInPredicate
  let declare ~file_name l = file_name, l
  let document_fmt fmt ?(calc=Setup.default_calc_descriptor) (_,l) =
    ED.BuiltInPredicate.document fmt l (List.rev !calc)
  let document_file ?header:_ ?(calc=Setup.default_calc_descriptor) (name,l) =
    let oc = open_out name in
    let fmt = Format.formatter_of_out_channel oc in
    ED.BuiltInPredicate.document fmt l (List.rev !calc);
    Format.pp_print_flush fmt ();
    close_out oc
end

module State = struct
  include ED.State
  let new_state_descriptor = ED.State.new_descriptor
  
  (* From now on, we pretend there is no difference between terms at
     compilation time and terms at execution time (in the API) *)
  let declare ~name ~pp ~init ~start =
    ED.State.declare ~descriptor:Setup.default_state_descriptor ~name ~pp ~init
      ~clause_compilation_is_over:(fun x -> x)
      ~goal_compilation_begins:(fun x -> start x)
      ~compilation_is_over:(fun x -> Some x)
      ~execution_is_over:(fun x -> Some x)
      ()

  let declare_component ?(descriptor=Setup.default_state_descriptor) ~name ~pp ~init ~start () =
    ED.State.declare ~descriptor ~name ~pp ~init
      ~clause_compilation_is_over:(fun x -> x)
      ~goal_compilation_begins:(fun x -> start x)
      ~compilation_is_over:(fun x -> Some x)
      ~execution_is_over:(fun x -> Some x)
      ()
    
end


module RawQuery = struct
  let compile_term p f = Compiler.query_of_scoped_term p (fun s -> let s, t = f s in s, Compiler_data.ScopedTerm.of_simple_term_loc t)
  let compile_raw_term p f = Compiler.query_of_raw_term p f
  let term_to_raw_term s p ?ctx ~depth t =
    let check = ED.State.get ED.while_compiling s in
    Compiler.compile_term_to_raw_term ~check s p ?ctx ~depth @@
    Compiler_data.ScopedTerm.of_simple_term_loc t
  let compile_ast = Compiler.query_of_ast
  (* let mk_Arg = Compiler.mk_Arg
  let is_Arg = Compiler.is_Arg *)
  let global_name_to_constant state s = Compiler.global_name_to_constant state s
end

module Quotation = struct
  type quotation = Compiler_data.QuotationHooks.quotation
  include Compiler
  let declare_backtick ?(descriptor=Setup.default_quotations_descriptor) ~name (f : quotation) =
    Compiler_data.QuotationHooks.declare_backtick_compilation ~descriptor name f

  let declare_singlequote ?(descriptor=Setup.default_quotations_descriptor) ~name f =
    Compiler_data.QuotationHooks.declare_singlequote_compilation ~descriptor name f

  let set_default_quotation ?(descriptor=Setup.default_quotations_descriptor) x = Compiler_data.QuotationHooks.set_default_quotation ~descriptor x

  let register_named_quotation ?(descriptor=Setup.default_quotations_descriptor) ~name x  = Compiler_data.QuotationHooks.register_named_quotation ~descriptor ~name x

  let new_quotations_descriptor = Compiler_data.QuotationHooks.new_descriptor

end

module Calc = struct

  let new_calc_descriptor = ED.CalcHooks.new_descriptor

  type operation_declaration = {
    symbol : string;
    infix : bool;
    args : string list list;
    code : ED.term list -> ED.term;
  }

  let compile_operation_declaration { symbol; infix; args; code } =
    let c = ED.Global_symbols.declare_global_symbol symbol in
    let ty_decl args =
     if infix then
       Printf.sprintf "type (%s) %s." symbol (String.concat " -> " args)
     else
       Printf.sprintf "type %s %s." symbol (String.concat " -> " args) in
     c, { ED.CalcHooks.ty_decl = List.map ty_decl args |> String.concat "\n"; code }

   let register ~descriptor d =
     let e = compile_operation_declaration d in
     descriptor := e :: !descriptor
    
  let register_eval n (symbol,tys) code =
    let infix, n = n < 0, abs n in
    let args = tys |> List.map (fun ty -> List.init (n+1) (fun _ -> ty)) in
    [{ symbol; infix; args; code }]
 
 let register_eval_ty symbol ty code =
   let infix = false in
   let args = [ty] in
   [{ symbol; infix; args; code }]


 let register_evals n l f = List.map (fun i -> register_eval n i f) l |> List.flatten
 
 let default_calc =
   let open Util in
   let open RawOpaqueData in
   List.flatten [
   register_evals ~-2 [ "-",["A"] ; "i-",["int"] ; "r-",["float"] ] (function
    | [ CData x; CData y ] when ty2 int x y -> (morph2 int (-) x y)
    | [ CData x; CData y ] when ty2 float x y -> (morph2 float (-.) x y)
    | _ -> type_error "Wrong arguments to -/i-/r-") ;
   register_evals ~-2 [ "+",["int";"float"] ; "i+",["int"] ; "r+",["float"] ] (function
    | [ CData x; CData y ] when ty2 int x y -> (morph2 int (+) x y)
    | [ CData x; CData y ] when ty2 float x y -> (morph2 float (+.) x y)
    | _ -> type_error "Wrong arguments to +/i+/r+") ;
   register_eval ~-2 ("*",["int";"float"]) (function
    | [ CData x; CData y ] when ty2 int x y -> (morph2 int ( * ) x y)
    | [ CData x; CData y] when ty2 float x y -> (morph2 float ( *.) x y)
    | _ -> type_error "Wrong arguments to *") ;
   register_eval ~-2 ("/",["float"]) (function
    | [ CData x; CData y] when ty2 float x y -> (morph2 float ( /.) x y)
    | _ -> type_error "Wrong arguments to /") ;
   register_eval ~-2 ("mod",["int"]) (function
    | [ CData x; CData y ] when ty2 int x y -> (morph2 int (mod) x y)
    | _ -> type_error "Wrong arguments to mod") ;
   register_eval ~-2 ("div",["int"]) (function
    | [ CData x; CData y ] when ty2 int x y -> (morph2 int (/) x y)
    | _ -> type_error "Wrong arguments to div") ;
   register_eval ~-2 ("^",["string"]) (function
    | [ CData x; CData y ] when ty2 string x y ->
          of_string (to_string x ^ to_string y)
    | _ -> type_error "Wrong arguments to ^") ;
   register_evals ~-1 [ "~",["int";"float"] ; "i~",["int"] ; "r~",["float"] ] (function
    | [ CData x ] when is_int x -> (morph1 int (~-) x)
    | [ CData x ] when is_float x -> (morph1 float (~-.) x)
    | _ -> type_error "Wrong arguments to ~/i~/r~") ;
   register_evals 1 [ "abs",["int";"float"] ; "iabs",["int"] ; "rabs",["float"] ] (function
    | [ CData x ] when is_int x -> (map int int abs x)
    | [ CData x ] when is_float x -> (map float float abs_float x)
    | _ -> type_error "Wrong arguments to abs/iabs/rabs") ;
   register_evals 2 [ "max",["int";"float"]] (function
    | [ CData x; CData y  ] when ty2 int x y -> (morph2 int max x y)
    | [ CData x; CData y  ] when ty2 float x y -> (morph2 float max x y)
    | _ -> type_error "Wrong arguments to abs/iabs/rabs") ;
   register_evals 2 [ "min",["int";"float"]] (function
    | [ CData x; CData y  ] when ty2 int x y -> (morph2 int min x y)
    | [ CData x; CData y  ] when ty2 float x y -> (morph2 float min x y)
    | _ -> type_error "Wrong arguments to abs/iabs/rabs") ;
   register_eval 1 ("sqrt",["float"]) (function
    | [ CData x ] when is_float x -> (map float float sqrt x)
    | _ -> type_error "Wrong arguments to sqrt") ;
   register_eval 1 ("sin",["float"]) (function
    | [ CData x ] when is_float x -> (map float float sin x)
    | _ -> type_error "Wrong arguments to sin") ;
   register_eval 1 ("cos",["float"]) (function
    | [ CData x ] when is_float x -> (map float float cos x)
    | _ -> type_error "Wrong arguments to cosin") ;
   register_eval 1 ("arctan",["float"]) (function
    | [ CData x ] when is_float x -> (map float float atan x)
    | _ -> type_error "Wrong arguments to arctan") ;
   register_eval 1 ("ln",["float"]) (function
    | [ CData x ] when is_float x -> (map float float log x)
    | _ -> type_error "Wrong arguments to ln") ;
   register_eval_ty "int_to_real" ["int";"float"] (function
    | [ CData x ] when is_int x -> (map int float float_of_int x)
    | _ -> type_error "Wrong arguments to int_to_real") ;
   register_eval_ty "floor" ["float";"int"] (function
    | [ CData x ] when is_float x ->
          (map float int (fun x -> int_of_float (floor x)) x)
    | _ -> type_error "Wrong arguments to floor") ;
   register_eval_ty "ceil" ["float";"int"] (function
    | [ CData x ] when is_float x ->
          (map float int (fun x -> int_of_float (ceil x)) x)
    | _ -> type_error "Wrong arguments to ceil") ;
   register_eval_ty "truncate" ["float";"int"] (function
    | [ CData x ] when is_float x -> (map float int truncate x)
    | _ -> type_error "Wrong arguments to truncate") ;
   register_eval_ty "size" ["string";"int"] (function
    | [ CData x ] when is_string x ->
          of_int (String.length (to_string x))
    | _ -> type_error "Wrong arguments to size") ;
   register_eval_ty "chr" ["int";"string"] (function
    | [ CData x ] when is_int x ->
          of_string (String.make 1 (char_of_int (to_int x)))
    | _ -> type_error "Wrong arguments to chr") ;
   register_eval_ty "rhc" ["string";"int"] (function
    | [ CData x ] when is_string x && String.length (to_string x) = 1 ->
        of_int (int_of_char (to_string x).[0])
    | _ -> type_error "Wrong arguments to rhc") ;
   register_eval_ty "string_to_int" ["string";"int"] (function
    | [ CData x ] when is_string x -> of_int (int_of_string (to_string x))
    | _ -> type_error "Wrong arguments to string_to_int") ;
   register_eval_ty "int_to_string" ["int";"string"] (function
    | [ CData x ] when is_int x ->
          of_string (string_of_int (to_int x))
    | _ -> type_error "Wrong arguments to int_to_string") ;
   register_eval_ty "substring" ["string";"int";"int";"string"] (function
    | [ CData x ; CData i ; CData j ] when is_string x && ty2 int i j ->
        let x = to_string x and i = to_int i and j = to_int j in
        if i >= 0 && j >= 0 && String.length x >= i+j then
          of_string (String.sub x i j)
        else type_error "Wrong arguments to substring"
    | _ -> type_error "Wrong argument type to substring") ;
   register_eval_ty "real_to_string" ["float";"string"] (function
    | [ CData x ] when is_float x ->
          of_string (string_of_float (to_float x))
    | _ -> type_error "Wrong arguments to real_to_string")
  ]

  let () = List.iter (register ~descriptor:Setup.default_calc_descriptor) default_calc

  let eval ~depth state x =
   let table = ED.State.get ED.CalcHooks.eval state in
   let lookup_eval c = Util.Constants.Map.find c table in
   let module R = (val !r) in let open R in
   let rec eval depth t =
     match deref_head ~depth t with
     | Lam _ -> Util.type_error "Evaluation of a lambda abstraction"
     | Builtin _ -> Util.type_error "Evaluation of built-in predicate"
     | App (hd,arg,args) ->
       let f =
         try lookup_eval hd
         with Not_found ->
           function
           | [] -> assert false
           | x::xs -> ED.mkApp hd x xs in
       let args = List.map (fun x -> eval depth x) (arg::args) in
       f args
     | AppUVar _ | UVar _ | Discard -> Util.error "Evaluation of a non closed term. Maybe delay this predicate call and declare a constraint."
     | Arg _ | AppArg _ -> Util.anomaly "Evaluation of a stack term"
     | Const hd as x ->
       let f =
         try lookup_eval hd
         with Not_found -> fun _ -> x in
       f []
     | (Nil | Cons _ as x) -> Util.type_error ("Lists cannot be evaluated: " ^ ED.show_term x)
     | CData _ as x -> x
 in
   eval depth x

 let calc =
   let open BuiltIn in
   let open ContextualConversion in
   let open BuiltInPredicate.Notation in
    [
    LPDoc " -- Evaluation --";

    LPCode "pred (is) o:A, i:A.";
    LPCode "X is Y :- calc Y X.";
  
    MLCode(Pred("calc",
      In(BuiltInData.poly "A",  "Expr",
      Out(BuiltInData.poly "A", "Out",
      Read(unit_ctx, "unifies Out with the value of Expr. It can be used in tandem with spilling, eg [f {calc (N + 1)}]"))),
        (fun t _ ~depth _ _ state -> !: (eval ~depth state t))),
    DocAbove);
    ]

end


module Utils = struct
  let lp_list_to_list ~depth t =
    let module R = (val !r) in let open R in
    lp_list_to_list ~depth t

  let list_to_lp_list tl =
    let module R = (val !r) in let open R in
    list_to_lp_list tl

  let get_assignment { ED.contents = t } =
    let module R = (val !r) in
    if t == ED.dummy then None
    else Some t

  let move ~from ~to_ t =
    let module R = (val !r) in let open R in
    hmove ~from ~to_ ?avoid:None t

  let beta = BuiltInPredicate.beta

  let error = Util.error
  let type_error = Util.type_error
  let anomaly = Util.anomaly
  let warn = Util.warn

  let clause_of_term ?name ?graft ~depth loc term =
    let open EA in
    let module Data = ED.Term in
    let module R = (val !r) in let open R in
    let show i = Format.asprintf "%a" (R.Pp.pp_constant ?pp_ctx:None) i in
    let buggy_loc = loc in
    (* Format.eprintf "clause: %a\n" ( Pp.uppterm depth [] ~argsdepth:0 ED.empty_env ) term; *)
    let rec aux d ctx t =
      match deref_head ~depth:d t with
      | Data.Const i when i >= 0 && i < depth ->
          error "program_of_term: the term is not closed"
      | Data.Const i when i < 0 ->
          Term.mkCon buggy_loc (show i)
      | Data.Const i -> Util.IntMap.find i ctx
      | Data.Lam t ->
          let s = "x" ^ string_of_int d in
          let ctx = Util.IntMap.add d (Term.mkCon buggy_loc s) ctx in
          Term.mkLam buggy_loc s None (aux (d+1) ctx t)
      | Data.App(c,x,xs) ->
          let c = aux d ctx (R.mkConst c) in
          let x = aux d ctx x in
          let xs = List.map (aux d ctx) xs in
          Term.mkApp loc (c :: x :: xs)
      | (Data.Arg _ | Data.AppArg _) -> assert false
      | Data.Cons(hd,tl) ->
          let hd = aux d ctx hd in
          let tl = aux d ctx tl in
          Term.mkSeq [hd;tl]
      | Data.Nil -> Term.mkNil buggy_loc
      | Data.Builtin(c,xs) ->
          let c = Term.mkCon buggy_loc (show c) in
          let xs = List.map (aux d ctx) xs in
          Term.mkApp loc (c :: xs)
      | Data.CData x -> Term.mkC buggy_loc x
      | (Data.UVar _ | Data.AppUVar _) ->
          error "program_of_term: the term contains uvars"
      | Data.Discard -> Term.mkCon buggy_loc "_"
    in
    let attributes =
      (match name with Some x -> [Name x] | None -> []) @
      (match graft with
        | Some (`After,x) -> [After x]
        | Some (`Before,x) -> [Before x]
        | Some (`Replace,x) -> [Replace x]
        | Some (`Remove,x) -> [Remove x]
        | None -> []) in
    [Program.Clause {
      Clause.loc = loc;
      attributes;
      body = aux depth Util.IntMap.empty term;
      needs_spilling = ();
    }]

  let term_to_raw_term s p ?ctx ~depth t =
    Compiler.runtime_hack_term_to_raw_term s p ?ctx ~depth @@
    Compiler_data.ScopedTerm.of_simple_term_loc t

  let map_acc = BuiltInData.map_acc

  module type Show = Util.Show
  module type ShowKey = Util.ShowKey
  module type Show1 = Util.Show1
  module Map = Util.Map
  module Set = Util.Set
  module IntSet = Util.IntSet
  module LocSet : Util.Set.S with type elt = Ast.Loc.t = Util.Set.Make(Ast.Loc)

end

module RawPp = struct
  let term depth fmt t =
    let module R = (val !r) in let open R in
    Pp.uppterm depth [] ~argsdepth:0 ED.empty_env fmt t

  let constraints f c = 
    let module R = (val !r) in let open R in
    Util.pplist ~boxed:true (pp_stuck_goal ?pp_ctx:None) "" f c

  let list = Util.pplist

  module Debug = struct
    let term depth fmt t =
      let module R = (val !r) in let open R in
       Pp.ppterm depth [] ~argsdepth:0 ED.empty_env fmt t
    let show_term = ED.show_term
  end
end
