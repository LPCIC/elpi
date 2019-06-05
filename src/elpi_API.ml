(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module type Runtime = module type of Elpi_runtime_trace_off.Elpi_runtime

let r = ref (module Elpi_runtime_trace_off.Elpi_runtime : Runtime)

let set_runtime = function
  | true  -> r := (module Elpi_runtime_trace_on.Elpi_runtime  : Runtime)
  | false -> r := (module Elpi_runtime_trace_off.Elpi_runtime : Runtime)

let set_trace argv =
  let args = Elpi_trace.parse_argv argv in
  set_runtime !Elpi_trace.debug;
  args

module Setup = struct

type builtins = string * Elpi_data.BuiltInPredicate.declaration list
type program_header = Elpi_ast.Program.t

let init ~builtins:(fname,decls) ~basedir:cwd argv =
  let new_argv = set_trace argv in
  let new_argv, paths =
    let rec aux args paths = function
      | [] -> List.rev args, List.rev paths
      | "-I" :: p :: rest -> aux args (p :: paths) rest
      | x :: rest -> aux (x :: args) paths rest
    in
      aux [] [] new_argv
  in
  Elpi_parser.init ~lp_syntax:Elpi_parser.lp_gramext ~paths ~cwd ();
  (* This is a bit ugly, since builtins are global but could be made
   * program specific *)
  List.iter (function
    | Elpi_data.BuiltInPredicate.MLCode (p,_) -> Elpi_data.BuiltInPredicate.register p
    | Elpi_data.BuiltInPredicate.MLData _ -> ()
    | Elpi_data.BuiltInPredicate.LPCode _ -> ()
    | Elpi_data.BuiltInPredicate.LPDoc _ -> ()) decls;
  (* This is a bit ugly, since we print and then parse... *)
  let b = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer b in
  Elpi_data.BuiltInPredicate.document fmt decls;
  Format.pp_print_flush fmt ();
  let text = Buffer.contents b in
  let strm = Stream.of_string text in
  let loc = Elpi_util.Loc.initial fname in
  let header =
    try
      Elpi_parser.parse_program_from_stream
        ~print_accumulated_files:false loc strm 
    with Elpi_parser.ParseError(loc,msg) ->
      List.iteri (fun i s ->
        Printf.eprintf "%4d: %s\n" (i+1) s)
        (Re.Str.(split_delim (regexp_string "\n") text));
      Printf.eprintf "Excerpt of %s:\n%s\n" fname
       (String.sub text loc.Elpi_util.Loc.line_starts_at
         Elpi_util.Loc.(loc.source_stop - loc.line_starts_at));
      Elpi_util.anomaly ~loc msg
  in
  header, new_argv

let trace args =
  match set_trace args with
  | [] -> ()
  | l -> Elpi_util.error ("Elpi_API.trace got unknown arguments: " ^ (String.concat " " l))

let usage =
  "\nParsing options:\n" ^
  "\t-I PATH  search for accumulated files in PATH\n" ^
  Elpi_trace.usage 

let set_warn = Elpi_util.set_warn
let set_error = Elpi_util.set_error
let set_anomaly = Elpi_util.set_anomaly
let set_type_error = Elpi_util.set_type_error
let set_std_formatter = Elpi_util.set_std_formatter
let set_err_formatter = Elpi_util.set_err_formatter

end

module Ast = struct
  type program = Elpi_ast.Program.t
  type query = Elpi_ast.Goal.t
  module Loc = Elpi_util.Loc
end

module Parse = struct
  let program ?(print_accumulated_files=false) =
    Elpi_parser.parse_program ~print_accumulated_files
  let program_from_stream ?(print_accumulated_files=false) =
    Elpi_parser.parse_program_from_stream ~print_accumulated_files
  let goal loc s = Elpi_parser.parse_goal ~loc s
  let goal_from_stream loc s = Elpi_parser.parse_goal_from_stream ~loc s
  exception ParseError = Elpi_parser.ParseError
end

module Data = struct
  type term = Elpi_data.term
  type constraints = Elpi_data.constraints
  type state = Elpi_data.State.t
  module StrMap = Elpi_util.StrMap
  type 'a solution = 'a Elpi_data.solution = {
    assignments : term StrMap.t;
    constraints : constraints;
    state : state;
    output : 'a;
  }
  type hyp = Elpi_data.clause_src = {
    hdepth : int;
    hsrc : term
  }
  type hyps = hyp list
end

module Compile = struct

  type program = Elpi_compiler.program
  type 'a query = 'a Elpi_compiler.query
  type 'a executable = 'a Elpi_data.executable

  let program ~flags header l =
    Elpi_compiler.program_of_ast ~flags (header @ List.flatten l)
  let query = Elpi_compiler.query_of_ast

  let static_check header ?checker ?flags p =
    let module R = (val !r) in let open R in
    let checker = Elpi_util.option_map List.flatten checker in
    Elpi_compiler.static_check header ~exec:(execute_once ~delay_outside_fragment:false) ?checker ?flags p

  module StrSet = Elpi_util.StrSet

  type flags = Elpi_compiler.flags = {
    defined_variables : StrSet.t;
    allow_untyped_builtin : bool;
    print_passes : bool;
  }
  let default_flags = Elpi_compiler.default_flags
  let link x = Elpi_compiler.executable_of_query x

  let dummy_header = []
end

module Execute = struct
  type 'a outcome = 'a Elpi_data.outcome =
    Success of 'a Data.solution | Failure | NoMoreSteps
  let once ?max_steps ?delay_outside_fragment p = 
    let module R = (val !r) in let open R in
    execute_once ?max_steps ?delay_outside_fragment p     
  let loop ?delay_outside_fragment p ~more ~pp =
    let module R = (val !r) in let open R in
    execute_loop ?delay_outside_fragment p ~more ~pp

end

module Pp = struct
  let term f t = (* XXX query depth *)
    let module R = (val !r) in let open R in
    R.Pp.uppterm 0 [] 0 [||] f t

  let constraints f c =
    let module R = (val !r) in let open R in
    Elpi_util.pplist ~boxed:true R.pp_stuck_goal "" f c

  let state = Elpi_data.State.pp

  let query f c =
    let module R = (val !r) in let open R in
    Elpi_compiler.pp_query (fun ~depth -> R.Pp.uppterm depth [] 0 [||]) f c

  module Ast = struct
    let program = Elpi_ast.Program.pp
  end
end

(****************************************************************************)

module Conversion = struct
  type extra_goals = Elpi_data.extra_goals
  include Elpi_data.Conversion
end

module RawOpaqueData = struct
  include Elpi_util.CData
  include Elpi_data.C

  type name = string
  type doc = string

  type 'a declaration = {
    name : name;
    doc : doc;
    pp : Format.formatter -> 'a -> unit;
    eq : 'a -> 'a -> bool;
    hash : 'a -> int;
    hconsed : bool;
    constants : (name * 'a) list; (* global constants of that type, eg "std_in" *)
  }

  let conversion_of_cdata ~name ?(doc="") ~constants
      { cin; isc; cout; name=c }
  =
  let ty = Conversion.TyName name in
  let embed ~depth:_ _ _ state x =
    state, Elpi_data.Term.CData (cin x), [] in
  let readback ~depth _ _ state t =
    let module R = (val !r) in let open R in
    match R.deref_head ~depth t with
    | Elpi_data.Term.CData c when isc c -> state, cout c
    | Elpi_data.Term.Const i as t when i < 0 ->
        begin try state, Elpi_data.Constants.Map.find i constants
        with Not_found -> raise (Conversion.TypeErr(ty,t)) end
    | t -> raise (Conversion.TypeErr(ty,t)) in
  let pp_doc fmt () =
    if doc <> "" then begin
      Elpi_data.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
      Format.fprintf fmt "@\n";
    end;
    (* TODO: use typeabbrv *)
    Format.fprintf fmt "@[<hov 2>macro %s :- ctype \"%s\".@]@\n@\n" name c;
    Elpi_data.Constants.Map.iter (fun c _ ->
      Format.fprintf fmt "@[<hov 2>type %a %s.@]@\n" Elpi_data.Constants.pp c name)
      constants
    in
  { Conversion.embed; readback; ty; pp_doc; pp = (fun fmt x -> pp fmt (cin x)) }

  let conversion_of_cdata ~name ?doc ?(constants=[]) cd =
    let prefix =
      if name = "int" || name = "float" || name = "string" then ""
      else "@" in
    let constants =
      List.fold_right (fun (n,v) ->
        Elpi_data.Constants.Map.add (Elpi_data.Constants.from_stringc n) v)
        constants Elpi_data.Constants.Map.empty in
    conversion_of_cdata ~name:(prefix^name) ?doc ~constants cd

  let declare { name; doc; pp; eq; hash; hconsed; constants; } =
    let cdata = declare {
      data_eq = eq;
      data_pp = pp;
      data_hash = hash;
      data_name = name;
      data_hconsed = hconsed;
   } in
   cdata, conversion_of_cdata ~name ~doc ~constants cdata

end


module OpaqueData = struct

  type name = string
  type doc = string

  type 'a declaration = 'a RawOpaqueData.declaration = {
    name : name;
    doc : doc;
    pp : Format.formatter -> 'a -> unit;
    eq : 'a -> 'a -> bool;
    hash : 'a -> int;
    hconsed : bool;
    constants : (name * 'a) list; (* global constants of that type, eg "std_in" *)
  }

  let declare x = snd @@ RawOpaqueData.declare x

end

module BuiltInData = struct

  let int    = RawOpaqueData.conversion_of_cdata ~name:"int"    Elpi_data.C.int
  let float  = RawOpaqueData.conversion_of_cdata ~name:"float"  Elpi_data.C.float
  let string = RawOpaqueData.conversion_of_cdata ~name:"string" Elpi_data.C.string
  let loc    = RawOpaqueData.conversion_of_cdata ~name:"loc"    Elpi_data.C.loc
  let poly ty =
    let embed ~depth:_ _ _ state x = state, x, [] in
    let readback ~depth _ _ state t = state, t in
    { Conversion.embed; readback; ty = Conversion.TyName ty;
      pp = (fun fmt _ -> Format.fprintf fmt "<poly>");
      pp_doc = (fun fmt () -> ()) }
  
  let any = poly "any"

  let map_acc_embed f s l =
    let rec aux acc accg s = function
    | [] -> s, List.rev acc, List.rev accg
    | x :: xs ->
        let s, x, eg = f s x in
        aux (x :: acc) (eg @ accg) s xs
    in
      aux [] [] s l
    
  let map_acc_readback f s l =
    let rec aux acc s = function
    | [] -> s, List.rev acc
    | x :: xs ->
        let s, x = f s x in
        aux (x :: acc) s xs
    in
      aux [] s l

  let list d =
    let embed ~depth h c s l =
      let module R = (val !r) in let open R in
      let s, l, eg = map_acc_embed (d.Conversion.embed ~depth h c) s l in
      s, list_to_lp_list l, eg in
    let readback ~depth h c s t =
      let module R = (val !r) in let open R in
      map_acc_readback (d.Conversion.readback ~depth h c) s
        (lp_list_to_list ~depth t)
    in
    let pp fmt l =
      Format.fprintf fmt "[%a]" (Elpi_util.pplist d.pp ~boxed:true "; ") l in
    { Conversion.embed; readback;
      ty = TyApp ("list",d.ty,[]);
      pp;
      pp_doc = (fun fmt () -> ()) }


end

module Elpi = struct
  type uvarHandle = Arg of string | Ref of Elpi_data.uvar_body
  [@@deriving show]

  type t = {
    handle : uvarHandle;
    lvl : int;
  }
  [@@deriving show]

  let lvl { lvl } = lvl 

  let equal { handle = h1; lvl = l1 } { handle = h2; lvl = l2 } =
    l1 == l2 &&
      match h1, h2 with
      | Ref p1, Ref p2 -> p1 == p2
      | Arg s1, Arg s2 -> String.equal s1 s2
      | _ -> false

  let compilation_is_over ~args k =
    match k.handle with
    | Ref _ -> assert false
    | Arg s -> { k with handle = Ref (Elpi_util.StrMap.find s args) }

  (* This is to hide to the client the fact that Args change representation
      after compilation *)
  let uvk = Elpi_data.State.declare ~name:"elpi:uvk" ~pp:(Elpi_util.StrMap.pp pp)
    ~compilation_is_over:(fun ~args x ->
        Some (Elpi_util.StrMap.map (compilation_is_over ~args) x))
    ~init:(fun () -> Elpi_util.StrMap.empty)

  let fresh_name =
    let i = ref 0 in
    fun () -> incr i; Printf.sprintf "_uvk_%d_" !i
  
  let alloc_Elpi name lvl state =            
    if Elpi_data.State.get Elpi_compiler.while_compiling state then
      let state, _arg = Elpi_compiler.mk_Arg ~name ~args:[] state in
      state, { lvl; handle = Arg name }
    else
      state, { lvl; handle = Ref (Elpi_data.oref Elpi_data.Constants.dummy) }

  let make ?name ~lvl state =
    match name with
    | None -> alloc_Elpi (fresh_name ()) lvl state
    | Some name ->
        try state, Elpi_util.StrMap.find name (Elpi_data.State.get uvk state) 
        with Not_found ->
          let state, k = alloc_Elpi name lvl state in
          Elpi_data.State.update uvk state (Elpi_util.StrMap.add name k), k

  let get ~name state =
    try Some (Elpi_util.StrMap.find name (Elpi_data.State.get uvk state))
    with Not_found -> None

end

module RawData = struct

  type constant = Elpi_data.Term.constant
  type builtin = Elpi_data.Term.constant
  type uvar_body = Elpi_data.Term.uvar_body
  type term = Elpi_data.Term.term
  type view =
    (* Pure subterms *)
    | Const of constant                   (* global constant or a bound var *)
    | Lam of term                         (* lambda abstraction, i.e. x\ *)
    | App of constant * term * term list  (* application (at least 1 arg) *)
    (* Optimizations *)
    | Cons of term * term                 (* :: *)
    | Nil                                 (* [] *)
    | Discard                             (* _  *)
    (* FFI *)
    | Builtin of builtin * term list      (* call to a built-in predicate *)
    | CData of RawOpaqueData.t                    (* external data *)
    (* Unassigned unification variables *)
    | UnifVar of Elpi.t * term list

  let look ~depth t =
    let module R = (val !r) in let open R in
    match R.deref_head ~depth t with
    | Elpi_data.Term.Arg _ | Elpi_data.Term.AppArg _ -> assert false
    | Elpi_data.Term.UVar(ub,lvl,nargs) ->
        let args = Elpi_data.Term.Constants.mkinterval 0 nargs 0 in
        UnifVar ({ lvl; handle = Ref ub},args)
    | Elpi_data.Term.AppUVar(ub,lvl,args) ->
        UnifVar ({ lvl; handle = Ref ub},args)
    | x -> Obj.magic x (* HACK: view is a "subtype" of Term.term *)

  let kool = function
    | UnifVar({ lvl; handle = Ref ub},args) -> Elpi_data.Term.AppUVar(ub,lvl,args)
    | UnifVar({ lvl; handle = Arg _},_) -> assert false
    | x -> Obj.magic x
  [@@ inline]

  let mkConst = Elpi_data.Term.mkConst
  let mkLam = Elpi_data.Term.mkLam
  let mkApp = Elpi_data.Term.mkApp
  let mkCons = Elpi_data.Term.mkCons
  let mkNil = Elpi_data.Term.mkNil
  let mkDiscard = Elpi_data.Term.mkDiscard
  let mkBuiltin = Elpi_data.Term.mkBuiltin
  let mkCData = Elpi_data.Term.mkCData
  let mkAppL = Elpi_data.Term.mkAppL
  let mkAppS = Elpi_data.Term.mkAppS
  let mkAppSL = Elpi_data.Term.mkAppSL
  
  let mkGlobalS s = Elpi_data.Term.Constants.from_string s
  let mkBuiltinS s args = mkBuiltin (Elpi_data.BuiltInPredicate.from_builtin_name s) args

  let mkGlobal i =
    if i >= 0 then Elpi_util.anomaly "mkGlobal: got a bound variable";
    mkConst i
  let mkBound i =
    if i < 0 then Elpi_util.anomaly "mkBound: got a global constant";
    mkConst i

  module Constants = Elpi_data.Term.Constants

  let of_term = Elpi_data.of_term

  let of_hyps x = x

  type hyp = Data.hyp = {
    hdepth : int;
    hsrc : term
  }
  type hyps = hyp list

  type suspended_goal = {
    context : hyps;
    goal : int * term
  }

  type constraints = Elpi_data.constraints
  
  let constraints = Elpi_util.map_filter (function
    | { Elpi_data.kind = Constraint { cdepth; conclusion; context } } ->
        Some { context ; goal = (cdepth, conclusion) }
    | _ -> None)
  let no_constraints = []

  let mkUnifVar { Elpi.handle; lvl } ~args state =
  match handle with
  | Elpi.Ref ub -> Elpi_data.Term.mkAppUVar ub lvl args
  | Elpi.Arg name -> Elpi_compiler.get_Arg state ~name ~args

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
  module Map = functor(T : Host) -> struct
    open Elpi_util

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

    let add ({ Elpi.lvl; handle } as uv) v { h2e; e2h_compile; e2h_run } =
      let h2e = H2E.add v uv h2e in
      match handle with
      | Elpi.Ref ub ->
          { h2e; e2h_compile; e2h_run = PtrMap.add ub v e2h_run }
      | Arg s ->
          { h2e; e2h_run; e2h_compile = StrMap.add s v e2h_compile }

    let elpi v { h2e } = H2E.find v h2e
    let host { Elpi.handle } { e2h_compile; e2h_run } =
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

    let remove_elpi ({ Elpi.handle } as k) m =
      let v = host k m in
      remove_both handle v m

    let remove_host v m =
      let { Elpi.handle } = elpi v m in
      remove_both handle v m

    let filter f { h2e; e2h_compile; e2h_run } =
      let e2h_compile = StrMap.filter (fun n v -> f v (H2E.find v h2e)) e2h_compile in
      let e2h_run = PtrMap.filter (fun ub v -> f v (H2E.find v h2e)) e2h_run in
      let h2e = H2E.filter f h2e in
      { h2e; e2h_compile; e2h_run }
      
    let fold f { h2e } acc =
      let module R = (val !r) in let open R in
      let get_val {Elpi.lvl; handle} =
        match handle with
        | Elpi.Ref { Elpi_data.Term.contents = ub }
          when ub != Elpi_data.Term.Constants.dummy ->
            Some (lvl, R.deref_head ~depth:lvl ub)
        | Elpi.Ref _ -> None
        | Elpi.Arg _ -> None in
      H2E.fold (fun k ({Elpi.lvl; handle} as uk) acc -> f k uk (get_val uk) acc) h2e acc

    let pp fmt (m : t) = Format.fprintf fmt "<uvm>"
    let show m = Format.asprintf "%a" pp m

    let uvmap = Elpi_data.State.declare ~name:"elpi:uvm" ~pp
      ~compilation_is_over:(fun ~args { h2e; e2h_compile; e2h_run } ->
        let h2e = H2E.map (Elpi.compilation_is_over ~args) h2e in
        let e2h_run =
          StrMap.fold (fun k v m ->
            PtrMap.add (StrMap.find k args) v m) e2h_compile (PtrMap.empty ()) in
        Some { h2e; e2h_compile = StrMap.empty; e2h_run })
      ~init:(fun () -> empty)

  end

  let uvar  = {
    Conversion.ty = Conversion.TyName "uvar";
    pp_doc = (fun fmt () -> Format.fprintf fmt "Unification variable, as the uvar keyword");
    pp = (fun fmt (k,_) -> Format.fprintf fmt "%a" Elpi.pp k);
    embed = (fun ~depth _ _ s (k,args) -> s, RawData.mkUnifVar k ~args s, []);
    readback = (fun ~depth _ _ state t ->
      match RawData.look ~depth t with
      | RawData.Discard ->
          let state, k = Elpi.make ~lvl:depth state in
          state, (k,[])
      | RawData.UnifVar(k,args) ->
          state, (k,args)
      | _ -> raise (Conversion.TypeErr (TyName "uvar",t)));
  }

end

module AlgebraicData = struct
  type name = string
  type doc = string

  include Elpi_data.BuiltInPredicate.ADT
  let declare x = 
    let look ~depth t =
      let module R = (val !r) in
      R.deref_head ~depth t in
    Elpi_data.BuiltInPredicate.adt
      ~look ~alloc:FlexibleData.Elpi.make ~mkUnifVar:RawData.mkUnifVar x
end

module BuiltInPredicate = struct
  include Elpi_data.BuiltInPredicate
  exception No_clause = Elpi_data.No_clause

  module Notation = struct

    let (!:) x = (), Some x
    let (+!) a b = a, Some b
    let (?:) x = (), x
    let (+?) a b = a, b

  end

end

module BuiltIn = struct
  include Elpi_data.BuiltInPredicate
  let declare ~file_name l = file_name, l
end

module Query = struct
  include Elpi_data.Query
  let compile = Elpi_compiler.query_of_data
end

module State = struct
  include Elpi_data.State
  (* From now on, we pretend there is no difference between terms at
     compilation time and terms at execution time (in the API) *)
  let declare ~name ~pp ~init =
    declare ~name ~pp ~init
      ~compilation_is_over:(fun ~args:_ x -> Some x)
end


module RawQuery = struct
  let mk_Arg = Elpi_compiler.mk_Arg
  let is_Arg = Elpi_compiler.is_Arg
  let compile = Elpi_compiler.query_of_term
end

module Quotation = struct
  include Elpi_compiler
  let declare_backtick ~name f =
    Elpi_data.CustomFunctorCompilation.declare_backtick_compilation name
      (fun s x -> f s (Elpi_ast.Func.show x))

  let declare_singlequote ~name f =
    Elpi_data.CustomFunctorCompilation.declare_singlequote_compilation name
      (fun s x -> f s (Elpi_ast.Func.show x))

  let term_at ~depth x = Elpi_compiler.term_of_ast ~depth x

end

module Utils = struct
  let lp_list_to_list ~depth t =
    let module R = (val !r) in let open R in
    lp_list_to_list ~depth t
          
  let list_to_lp_list tl =
    let module R = (val !r) in let open R in
    list_to_lp_list tl

  let get_assignment { Elpi.handle } =
    match handle with
    | Elpi.Arg _ -> assert false
    | Elpi.Ref { Elpi_data.contents = r } ->
        if r == Elpi_data.Constants.dummy then None
        else Some r

  let move ~from ~to_ t =
    let module R = (val !r) in let open R in
    R.hmove ~from ~to_ ?avoid:None t
  
  let error = Elpi_util.error
  let type_error = Elpi_util.type_error
  let anomaly = Elpi_util.anomaly
  let warn = Elpi_util.warn

  let clause_of_term ?name ?graft ~depth loc term =
    let open Elpi_ast in
    let module Data = Elpi_data.Term in
    let module R = (val !r) in let open R in
    let rec aux d ctx t =
      match R.deref_head ~depth:d t with       
      | Data.Const i when i >= 0 && i < depth ->
          error "program_of_term: the term is not closed"
      | Data.Const i when i < 0 ->
          Term.mkCon (Data.Constants.show i)
      | Data.Const i -> Elpi_util.IntMap.find i ctx
      | Data.Lam t ->
          let s = "x" ^ string_of_int d in
          let ctx = Elpi_util.IntMap.add d (Term.mkCon s) ctx in
          Term.mkLam s (aux (d+1) ctx t)
      | Data.App(c,x,xs) ->
          let c = aux d ctx (Data.Constants.mkConst c) in
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
          let c = aux d ctx (Data.Constants.mkConst c) in
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
      body = aux depth Elpi_util.IntMap.empty term;
    }]

  let map_acc_embed = BuiltInData.map_acc_embed
  let map_acc_readback = BuiltInData.map_acc_readback

end

module RawPp = struct
  let term depth fmt t =
    let module R = (val !r) in let open R in
    R.Pp.uppterm depth [] 0 Elpi_data.empty_env fmt t

  let constraint_ f c = 
    let module R = (val !r) in let open R in
    R.pp_stuck_goal f c

  let list = Elpi_util.pplist

  module Debug = struct
    let term depth fmt t =
      let module R = (val !r) in let open R in
      R.Pp.ppterm depth [] 0 Elpi_data.empty_env fmt t
    let show_term = Elpi_data.show_term
  end
end