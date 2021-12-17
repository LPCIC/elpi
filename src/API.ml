(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module type Runtime = (module type of Runtime_trace_off)

let r = ref (module Runtime_trace_off : Runtime)

let set_runtime b =
  begin match b with
  | true  -> r := (module Runtime  : Runtime)
  | false -> r := (module Runtime_trace_off : Runtime)
  end;
  let module R = (val !r) in
  Util.set_spaghetti_printer Data.pp_const R.Pp.pp_constant

let set_trace argv =
  let args = Trace_ppx_runtime.Runtime.parse_argv argv in
  set_runtime !Trace_ppx_runtime.Runtime.debug;
  args

module Setup = struct

type builtins = Compiler.builtins
type elpi = Parser.parser_state * Compiler.header
type flags = Compiler.flags

let init ?(flags=Compiler.default_flags) ~builtins ~basedir:cwd argv =
  let new_argv = set_trace argv in
  let new_argv, paths =
    let rec aux args paths = function
      | [] -> List.rev args, List.rev paths
      | "-I" :: p :: rest -> aux args (p :: paths) rest
      | x :: rest -> aux (x :: args) paths rest
    in
      aux [] [] new_argv
  in
  (* At the moment we can only init the parser once *)
  let parsing_state = Parser.init ~lp_syntax:Parser.lp_gramext ~paths ~cwd in
  Data.Global_symbols.lock ();
  let header_src =
    builtins |> List.map (fun (fname,decls) ->
      (* This is a bit ugly, since we print and then parse... *)
      let b = Buffer.create 1024 in
      let fmt = Format.formatter_of_buffer b in
      Data.BuiltInPredicate.document fmt decls;
      Format.pp_print_flush fmt ();
      let text = Buffer.contents b in
      let strm = Stream.of_string text in
      let loc = Util.Loc.initial fname in
      try
        Parser.parse_program_from_stream parsing_state
          ~print_accumulated_files:false loc strm
      with Parser.ParseError(loc,msg) ->
        List.iteri (fun i s ->
          Printf.eprintf "%4d: %s\n" (i+1) s)
          (Re.Str.(split_delim (regexp_string "\n") text));
        Printf.eprintf "Excerpt of %s:\n%s\n" fname
          (String.sub text loc.Util.Loc.line_starts_at
            Util.Loc.(loc.source_stop - loc.line_starts_at));
      Util.anomaly ~loc msg) in
  let header =
    try Compiler.header_of_ast ~flags builtins (List.concat header_src)
    with Compiler.CompileError(loc,msg) -> Util.anomaly ?loc msg in
  (parsing_state, header), new_argv

let trace args =
  match set_trace args with
  | [] -> ()
  | l -> Util.error ("Elpi_API.trace got unknown arguments: " ^ (String.concat " " l))

let usage =
  "\nParsing options:\n" ^
  "\t-I PATH  search for accumulated files in PATH\n" ^
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
end

module Parse = struct
  let program ~elpi:(ps,_) ?(print_accumulated_files=false) =
    Parser.parse_program ps ~print_accumulated_files
  let program_from_stream ~elpi:(ps,_) ?(print_accumulated_files=false) =
    Parser.parse_program_from_stream ps ~print_accumulated_files
  let goal loc s = Parser.parse_goal ~loc s
  let goal_from_stream loc s = Parser.parse_goal_from_stream ~loc s
  exception ParseError = Parser.ParseError

  let resolve_file f = snd @@ Parser.resolve f
end

module ED = Data

module Data = struct
  type term = Data.term
  type constraints = Data.constraints
  type state = Data.State.t
  type pretty_printer_context = ED.pp_ctx
  module StrMap = Util.StrMap
  type 'a solution = 'a Data.solution = {
    assignments : term StrMap.t;
    constraints : constraints;
    state : state;
    output : 'a;
    pp_ctx : pretty_printer_context;
  }
  type hyp = Data.clause_src = {
    hdepth : int;
    hsrc : term
  }
  type hyps = hyp list
end

module Compile = struct

  type program = Compiler.program
  type 'a query = 'a Compiler.query
  type 'a executable = 'a ED.executable
  type compilation_unit = Compiler.compilation_unit
  exception CompileError = Compiler.CompileError

  let to_setup_flags x = x

  let program ?(flags=Compiler.default_flags) ~elpi:(_,header) l =
    Compiler.program_of_ast ~flags ~header (List.flatten l)

  let query s_p t =
    Compiler.query_of_ast s_p t

  let static_check ~checker q =
    let module R = (val !r) in let open R in
    Compiler.static_check ~exec:(execute_once ~delay_outside_fragment:false) ~checker q

  module StrSet = Util.StrSet

  type flags = Compiler.flags = {
    defined_variables : StrSet.t;
    print_passes : bool;
    print_units : bool;
  }
  let default_flags = Compiler.default_flags
  let optimize = Compiler.optimize_query
  let unit ?(flags=Compiler.default_flags) ~elpi:(_,header) x = Compiler.unit_of_ast ~flags ~header x
  let extend ?(flags=Compiler.default_flags) ~base ul = Compiler.append_units ~flags ~base ul
  let assemble ?(flags=Compiler.default_flags) ~elpi:(_,header) = Compiler.assemble_units ~flags ~header

end

module Execute = struct
  type 'a outcome = 'a ED.outcome =
    Success of 'a Data.solution | Failure | NoMoreSteps
  let once ?max_steps ?delay_outside_fragment p =
    let module R = (val !r) in
    R.execute_once ?max_steps ?delay_outside_fragment p
  let loop ?delay_outside_fragment p ~more ~pp =
    let module R = (val !r) in
    R.execute_loop ?delay_outside_fragment p ~more ~pp

end

module Pp = struct
  let term pp_ctx f t = (* XXX query depth *)
    let module R = (val !r) in let open R in
    R.Pp.uppterm ~pp_ctx 0 [] ~argsdepth:0 [||] f t

  let constraints pp_ctx f c =
    let module R = (val !r) in let open R in
    Util.pplist ~boxed:true R.(pp_stuck_goal ~pp_ctx) "" f c

  let state = ED.State.pp

  let query f c =
    let module R = (val !r) in let open R in
    Compiler.pp_query (fun ~pp_ctx ~depth -> R.Pp.uppterm ~pp_ctx depth [] ~argsdepth:0 [||]) f c

  module Ast = struct
    let program = EA.Program.pp
  end
end

(****************************************************************************)

module Conversion = struct
  type extra_goals = ED.extra_goals
  include ED.Conversion
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
    isc : t -> bool;
    cout: t -> 'a;
    name : string;
  }

  let conversion_of_cdata ~name ?(doc="") ~constants_map ~values_map ~constants
     ~pp ({ Util.CData.cin; isc; cout; name = c } )
  =
  let ty = Conversion.TyName name in
  let cin x =
    let module R = (val !r) in
    try R.mkConst (values_map x)
    with Not_found -> ED.Term.CData (cin x) in
  let embed ~depth:_ state x =
    state, cin x, [] in
  let readback ~depth state t =
    let module R = (val !r) in let open R in
    match R.deref_head ~depth t with
    | ED.Term.CData c when isc c -> state, cout c, []
    | ED.Term.Const i as t when i < 0 ->
        begin try state, ED.Constants.Map.find i constants_map, []
        with Not_found -> raise (Conversion.TypeErr(ty,depth,t)) end
    | t -> raise (Conversion.TypeErr(ty,depth,t)) in
  let pp_doc fmt () =
    let module R = (val !r) in let open R in
    if doc <> "" then begin
      ED.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
      Format.fprintf fmt "@\n";
    end;
    Format.fprintf fmt "@[<hov 2>typeabbrev %s (ctype \"%s\").@]@\n@\n" name c;
    List.iter (fun (c,_) ->
      Format.fprintf fmt "@[<hov 2>type %s %s.@]@\n" c name)
      constants
    in
  { cin; cout; isc; name = c },
  { Conversion.embed; readback; ty; pp_doc; pp }

  let conversion_of_cdata (type a) ~name ?doc ?(constants=[]) ~compare ~pp cd =
    let module R = (val !r) in let open R in
    let module VM = Map.Make(struct type t = a let compare = compare end) in
    let constants_map, values_map =
      List.fold_right (fun (n,v) (cm,vm) ->
        let c = ED.Global_symbols.declare_global_symbol n in
        ED.Constants.Map.add c v cm, VM.add v c vm)
      constants (ED.Constants.Map.empty,VM.empty) in
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
     { cin = (fun x -> ED.mkCData (cin x)); cout; isc; name }
   let is_int = ED.C.is_int
   let to_int = ED.C.to_int
   let of_int = ED.C.of_int
   let float =
     let { Util.CData.cin; cout; isc; name } = ED.C.float in
     { cin = (fun x -> ED.mkCData (cin x)); cout; isc; name }
   let is_float = ED.C.is_float
   let to_float = ED.C.to_float
   let of_float = ED.C.of_float
   let string =
     let { Util.CData.cin; cout; isc; name } = ED.C.string in
     { cin = (fun x -> ED.mkCData (cin x)); cout; isc; name }
   let is_string = ED.C.is_string
   let to_string = ED.C.to_string
   let of_string = ED.C.of_string
   let loc =
     let { Util.CData.cin; cout; isc; name } = ED.C.loc in
     { cin = (fun x -> ED.mkCData (cin x)); cout; isc; name }
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
  let float  = snd @@ RawOpaqueData.conversion_of_cdata ~name:"float"  ~compare:Pervasives.compare (*Float.compare*)      ~pp:(fun fmt x -> Util.CData.pp fmt (ED.C.float.Util.CData.cin x)) ED.C.float
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
      state, R.hmove ~from ~to_:depth ?avoid:None x, [] in
    let readback ~depth state t =
      state, fresh_copy t depth, [] in
    { Conversion.embed; readback; ty;
      pp = (fun fmt (t,d) ->
        let module R = (val !r) in let open R in
        R.Pp.uppterm d [] d ED.empty_env fmt t);
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

  type t = Arg of string | Ref of ED.uvar_body

  let pp fmt handle =
    match handle with
    | Arg str ->
        Format.fprintf fmt "%s" str
    | Ref ub ->
        let module R = (val !r) in let open R in
        R.Pp.uppterm 0 [] 0 [||] fmt (ED.mkUVar ub 0 0)

  let show m = Format.asprintf "%a" pp m

  let equal h1 h2  =
      match h1, h2 with
      | Ref p1, Ref p2 -> p1 == p2
      | Arg s1, Arg s2 -> String.equal s1 s2
      | _ -> false

  let compilation_is_over ~args k =
    match k with
    | Ref _ -> assert false
    | Arg s -> Ref (Util.StrMap.find s args)

  (* This is to hide to the client the fact that Args change representation
      after compilation *)
  let uvk = ED.State.declare ~name:"elpi:uvk" ~pp:(Util.StrMap.pp pp)
    ~clause_compilation_is_over:(fun x -> Util.StrMap.empty)
    ~goal_compilation_begins:(fun x -> Util.StrMap.empty)
    ~goal_compilation_is_over:(fun ~args x ->
        Some (Util.StrMap.map (compilation_is_over ~args) x))
    ~compilation_is_over:(fun _ -> None)
    ~execution_is_over:(fun _ -> None)
    ~init:(fun () -> Util.StrMap.empty)

  let fresh_name =
    let i = ref 0 in
    fun () -> incr i; Printf.sprintf "_uvk_%d_" !i

  let alloc_Elpi name state =
    if ED.State.get ED.while_compiling state then
      let state, _arg = Compiler.mk_Arg ~name ~args:[] state in
      state, Arg name
    else
      let module R = (val !r) in
      state, Ref (ED.oref ED.dummy)

  let make ?name state =
    match name with
    | None -> alloc_Elpi (fresh_name ()) state
    | Some name ->
        try state, Util.StrMap.find name (ED.State.get uvk state)
        with Not_found ->
          let state, k = alloc_Elpi name state in
          ED.State.update uvk state (Util.StrMap.add name k), k

  let get ~name state =
    try Some (Util.StrMap.find name (ED.State.get uvk state))
    with Not_found -> None

end

module RawData = struct

  type constant = ED.Term.constant
  type builtin = ED.Term.constant
  type uvar_body = ED.Term.uvar_body
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

  let rec look ~depth t =
    let module R = (val !r) in let open R in
    match R.deref_head ~depth t with
    | ED.Term.Arg _ | ED.Term.AppArg _ -> assert false
    | ED.Term.AppUVar(ub,0,args) -> UnifVar (Ref ub,args)
    | ED.Term.AppUVar(ub,lvl,args) -> look ~depth (R.expand_appuv ub ~depth ~lvl ~args)
    | ED.Term.UVar(ub,lvl,ano) -> look ~depth (R.expand_uv ub ~depth ~lvl ~ano)
    | ED.Term.Discard ->
        let ub = ED.oref ED.dummy in
        UnifVar (Ref ub,R.mkinterval 0 depth 0)
    | ED.Term.Lam _ as t ->
        begin match R.eta_contract_flex ~depth t with
        | None -> Obj.magic t (* HACK: view is a "subtype" of Term.term *)
        | Some t -> look ~depth t
        end
    | x -> Obj.magic x (* HACK: view is a "subtype" of Term.term *)

  let kool = function
    | UnifVar(Ref ub,args) -> ED.Term.AppUVar(ub,0,args)
    | UnifVar(Arg _,_) -> assert false
    | x -> Obj.magic x
  [@@ inline]

  let mkConst n = let module R = (val !r) in R.mkConst n
  let mkLam = ED.Term.mkLam
  let mkApp = ED.Term.mkApp
  let mkCons = ED.Term.mkCons
  let mkNil = ED.Term.mkNil
  let mkDiscard = ED.Term.mkDiscard
  let mkBuiltin = ED.Term.mkBuiltin
  let mkCData = ED.Term.mkCData
  let mkAppL x l = let module R = (val !r) in R.mkAppL x l

  let mkGlobal i =
    if i >= 0 then Util.anomaly "mkGlobal: got a bound variable";
    mkConst i
  let mkBound i =
    if i < 0 then Util.anomaly "mkBound: got a global constant";
    mkConst i

  let cmp_builtin i j = i - j

  module Constants = struct

    let declare_global_symbol = ED.Global_symbols.declare_global_symbol

    let show c = ED.Constants.show c

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

    module Map = ED.Constants.Map
    module Set = ED.Constants.Set

  end

  let of_term x = x

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

  type constraints = Data.constraints

  let constraints l =
    let module R = (val !r) in let open R in
    Util.map_filter (fun x -> R.get_suspended_goal x.ED.kind) l
  let no_constraints = []

  let mkUnifVar handle ~args state =
  match handle with
  | Elpi.Ref ub -> ED.Term.mkAppUVar ub 0 args
  | Elpi.Arg name -> Compiler.get_Arg state ~name ~args

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
        e2h_compile : T.t StrMap.t;
        e2h_run : T.t PtrMap.t
    }

    let empty = {
      h2e = H2E.empty;
      e2h_compile = StrMap.empty;
      e2h_run = PtrMap.empty ()
    }

    let add uv v { h2e; e2h_compile; e2h_run } =
      let h2e = H2E.add v uv h2e in
      match uv with
      | Elpi.Ref ub ->
          { h2e; e2h_compile; e2h_run = PtrMap.add ub v e2h_run }
      | Arg s ->
          { h2e; e2h_run; e2h_compile = StrMap.add s v e2h_compile }

    let elpi v { h2e } = H2E.find v h2e
    let host handle { e2h_compile; e2h_run } =
      match handle with
      | Elpi.Ref ub -> PtrMap.find ub e2h_run
      | Arg s -> StrMap.find s e2h_compile

    let remove_both handle v { h2e; e2h_compile; e2h_run } = 
      let h2e = H2E.remove v h2e in
      match handle with
      | Elpi.Ref ub ->
          { h2e; e2h_compile; e2h_run = PtrMap.remove ub e2h_run }
      | Arg s ->
          { h2e; e2h_run; e2h_compile = StrMap.remove s e2h_compile }

    let remove_elpi k m =
      let v = host k m in
      remove_both k v m

    let remove_host v m =
      let handle = elpi v m in
      remove_both handle v m

    let filter f { h2e; e2h_compile; e2h_run } =
      let e2h_compile = StrMap.filter (fun n v -> f v (H2E.find v h2e)) e2h_compile in
      let e2h_run = PtrMap.filter (fun ub v -> f v (H2E.find v h2e)) e2h_run in
      let h2e = H2E.filter f h2e in
      { h2e; e2h_compile; e2h_run }

    let fold f { h2e } acc =
      let module R = (val !r) in let open R in
      let get_val = function
        | Elpi.Ref { ED.Term.contents = ub }
          when ub != ED.dummy ->
            Some (R.deref_head ~depth:0 ub)
        | Elpi.Ref _ -> None
        | Elpi.Arg _ -> None in
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

    let uvmap = ED.State.declare ~name:(Printf.sprintf "elpi:uvm:%d" uvn) ~pp
      ~clause_compilation_is_over:(fun x -> empty)
      ~goal_compilation_begins:(fun x -> x)
      ~goal_compilation_is_over:(fun ~args { h2e; e2h_compile; e2h_run } ->
        let h2e = H2E.map (Elpi.compilation_is_over ~args) h2e in
        let e2h_run =
          StrMap.fold (fun k v m ->
            PtrMap.add (StrMap.find k args) v m) e2h_compile (PtrMap.empty ()) in
        Some { h2e; e2h_compile = StrMap.empty; e2h_run })
      ~compilation_is_over:(fun x -> Some x)
      ~execution_is_over:(fun x -> Some x)
      ~init:(fun () -> empty)

  end

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
               match R.deref_head ~depth t with
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
             match R.deref_head ~depth t with
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
end

module BuiltIn = struct
  include ED.BuiltInPredicate
  let declare ~file_name l = file_name, l
  let document_fmt fmt (_,l) =
    ED.BuiltInPredicate.document fmt l
  let document_file ?(header="") (name,l) =
    let oc = open_out name in
    let fmt = Format.formatter_of_out_channel oc in
    Format.fprintf fmt "%s%!" header;
    ED.BuiltInPredicate.document fmt l;
    Format.pp_print_flush fmt ();
    close_out oc
end

module Query = struct
  type name = string
  type 'f arguments = 'f ED.Query.arguments =
    | N : unit arguments
    | D : 'a Conversion.t * 'a *    'x arguments -> 'x arguments
    | Q : 'a Conversion.t * name * 'x arguments -> ('a * 'x) arguments

  type 'x t = Query of { predicate : name; arguments : 'x arguments }

  let compile p loc (Query { predicate; arguments }) =
    let p, predicate = Compiler.lookup_query_predicate p predicate in
    let q = ED.Query.Query{ predicate; arguments } in
    Compiler.query_of_data p loc q
end

module State = struct
  include ED.State
  (* From now on, we pretend there is no difference between terms at
     compilation time and terms at execution time (in the API) *)
  let declare ~name ~pp ~init ~start =
    declare ~name ~pp ~init
      ~clause_compilation_is_over:(fun x -> x)
      ~goal_compilation_begins:(fun x -> start x)
      ~goal_compilation_is_over:(fun ~args:_ x -> Some x)
      ~compilation_is_over:(fun x -> Some x)
      ~execution_is_over:(fun x -> Some x)

end


module RawQuery = struct
  let mk_Arg = Compiler.mk_Arg
  let is_Arg = Compiler.is_Arg
  let compile = Compiler.query_of_term
end

module Quotation = struct
  include Compiler
  let declare_backtick ~name f =
    Compiler.CustomFunctorCompilation.declare_backtick_compilation name
      (fun s x -> f s (EA.Func.show x))

  let declare_singlequote ~name f =
    Compiler.CustomFunctorCompilation.declare_singlequote_compilation name
      (fun s x -> f s (EA.Func.show x))

  let term_at ~depth s x = Compiler.term_of_ast ~depth s x

  let quote_syntax_runtime s q =
    let module R = (val !r) in
    Compiler.quote_syntax (`Runtime R.mkConst) s q
  let quote_syntax_compiletime s q =
    let s, l, t = Compiler.quote_syntax `Compiletime s q in
    s, l, t

end

module Utils = struct
  let lp_list_to_list ~depth t =
    let module R = (val !r) in let open R in
    lp_list_to_list ~depth t

  let list_to_lp_list tl =
    let module R = (val !r) in let open R in
    list_to_lp_list tl

  let get_assignment = function
    | Elpi.Arg _ -> assert false
    | Elpi.Ref { ED.contents = t } ->
        let module R = (val !r) in
        if t == ED.dummy then None
        else Some t

  let move ~from ~to_ t =
    let module R = (val !r) in let open R in
    R.hmove ~from ~to_ ?avoid:None t
  let beta ~depth t args =
    let module R = (val !r) in let open R in
    R.deref_appuv ~from:depth ~to_:depth ?avoid:None args t

  let error = Util.error
  let type_error = Util.type_error
  let anomaly = Util.anomaly
  let warn = Util.warn

  let clause_of_term ?name ?graft ~depth loc term =
    let open EA in
    let module Data = ED.Term in
    let module R = (val !r) in let open R in
    let rec aux d ctx t =
      match R.deref_head ~depth:d t with
      | Data.Const i when i >= 0 && i < depth ->
          error "program_of_term: the term is not closed"
      | Data.Const i when i < 0 ->
          Term.mkCon (ED.Constants.show i)
      | Data.Const i -> Util.IntMap.find i ctx
      | Data.Lam t ->
          let s = "x" ^ string_of_int d in
          let ctx = Util.IntMap.add d (Term.mkCon s) ctx in
          Term.mkLam s (aux (d+1) ctx t)
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
      | Data.Nil -> Term.mkNil
      | Data.Builtin(c,xs) ->
          let c = Term.mkCon (ED.Constants.show c) in
          let xs = List.map (aux d ctx) xs in
          Term.mkApp loc (c :: xs)
      | Data.CData x -> Term.mkC x
      | (Data.UVar _ | Data.AppUVar _) ->
          error "program_of_term: the term contains uvars"
      | Data.Discard -> Term.mkCon "_"
    in
    let attributes =
      (match name with Some x -> [Clause.Name x] | None -> []) @
      (match graft with
        | Some (`After,x) -> [Clause.After x]
        | Some (`Before,x) -> [Clause.Before x]
        | None -> []) in
    [Program.Clause {
      Clause.loc = loc;
      attributes;
      body = aux depth Util.IntMap.empty term;
    }]

  let map_acc = BuiltInData.map_acc

  module type Show = Util.Show
  module type Show1 = Util.Show1
  module Map = Util.Map
  module Set = Util.Set

end

module RawPp = struct
  let term depth fmt t =
    let module R = (val !r) in let open R in
    R.Pp.uppterm depth [] 0 ED.empty_env fmt t

  let constraints f c = 
    let module R = (val !r) in let open R in
    Util.pplist ~boxed:true (R.pp_stuck_goal ?pp_ctx:None) "" f c

  let list = Util.pplist

  module Debug = struct
    let term depth fmt t =
      let module R = (val !r) in let open R in
      R.Pp.ppterm depth [] 0 ED.empty_env fmt t
    let show_term = ED.show_term
  end
end
