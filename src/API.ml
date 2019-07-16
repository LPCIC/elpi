(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module type Runtime = module type of Runtime_trace_off

let r = ref (module Runtime_trace_off : Runtime)

let set_runtime = function
  | true  -> r := (module Runtime_trace_on  : Runtime)
  | false -> r := (module Runtime_trace_off : Runtime)

let set_trace argv =
  let args = Trace.Runtime.parse_argv argv in
  set_runtime !Trace.Runtime.debug;
  args

module Setup = struct

type builtins = string * Data.BuiltInPredicate.declaration list
type program_header = Ast.Program.t

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
  Parser.init ~lp_syntax:Parser.lp_gramext ~paths ~cwd ();
  (* This is a bit ugly, since builtins are global but could be made
   * program specific *)
  List.iter (function
    | Data.BuiltInPredicate.MLCode (p,_) -> Data.BuiltInPredicate.register p
    | Data.BuiltInPredicate.MLData _ -> ()
    | Data.BuiltInPredicate.LPCode _ -> ()
    | Data.BuiltInPredicate.LPDoc _ -> ()) decls;
  (* This is a bit ugly, since we print and then parse... *)
  let b = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer b in
  Data.BuiltInPredicate.document fmt decls;
  Format.pp_print_flush fmt ();
  let text = Buffer.contents b in
  let strm = Stream.of_string text in
  let loc = Util.Loc.initial fname in
  let header =
    try
      Parser.parse_program_from_stream
        ~print_accumulated_files:false loc strm 
    with Parser.ParseError(loc,msg) ->
      List.iteri (fun i s ->
        Printf.eprintf "%4d: %s\n" (i+1) s)
        (Re.Str.(split_delim (regexp_string "\n") text));
      Printf.eprintf "Excerpt of %s:\n%s\n" fname
       (String.sub text loc.Util.Loc.line_starts_at
         Util.Loc.(loc.source_stop - loc.line_starts_at));
      Util.anomaly ~loc msg
  in
  header, new_argv

let trace args =
  match set_trace args with
  | [] -> ()
  | l -> Util.error ("Elpi_API.trace got unknown arguments: " ^ (String.concat " " l))

let usage =
  "\nParsing options:\n" ^
  "\t-I PATH  search for accumulated files in PATH\n" ^
  Trace.Runtime.usage 

let set_warn = Util.set_warn
let set_error = Util.set_error
let set_anomaly = Util.set_anomaly
let set_type_error = Util.set_type_error
let set_std_formatter = Util.set_std_formatter
let set_err_formatter fmt =
  Util.set_err_formatter fmt; Trace.Runtime.set_formatter fmt

end

module EA = Ast

module Ast = struct
  type program = Ast.Program.t
  type query = Ast.Goal.t
  module Loc = Util.Loc
end

module Parse = struct
  let program ?(print_accumulated_files=false) =
    Parser.parse_program ~print_accumulated_files
  let program_from_stream ?(print_accumulated_files=false) =
    Parser.parse_program_from_stream ~print_accumulated_files
  let goal loc s = Parser.parse_goal ~loc s
  let goal_from_stream loc s = Parser.parse_goal_from_stream ~loc s
  exception ParseError = Parser.ParseError
end

module ED = Data

module Data = struct
  type term = Data.term
  type constraints = Data.constraints
  type state = Data.State.t
  module StrMap = Util.StrMap
  type 'a solution = 'a Data.solution = {
    assignments : term StrMap.t;
    constraints : constraints;
    state : state;
    output : 'a;
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

  let program ~flags header l =
    Compiler.program_of_ast ~flags (header @ List.flatten l)
  let query = Compiler.query_of_ast

  let static_check header ?checker ?flags p =
    let module R = (val !r) in let open R in
    let checker = Util.option_map List.flatten checker in
    Compiler.static_check header ~exec:(execute_once ~delay_outside_fragment:false) ?checker ?flags p

  module StrSet = Util.StrSet

  type flags = Compiler.flags = {
    defined_variables : StrSet.t;
    allow_untyped_builtin : bool;
    print_passes : bool;
  }
  let default_flags = Compiler.default_flags
  let link x = Compiler.executable_of_query x

  let dummy_header = []
end

module Execute = struct
  type 'a outcome = 'a ED.outcome =
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
    Util.pplist ~boxed:true R.pp_stuck_goal "" f c

  let state = ED.State.pp

  let query f c =
    let module R = (val !r) in let open R in
    Compiler.pp_query (fun ~depth -> R.Pp.uppterm depth [] 0 [||]) f c

  module Ast = struct
    let program = EA.Program.pp
  end
end

(****************************************************************************)

module Conversion = struct
  type extra_goals = ED.extra_goals
  include ED.Conversion
end

module RawOpaqueData = struct
  include Util.CData
  include ED.C

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
    state, ED.Term.CData (cin x), [] in
  let readback ~depth _ _ state t =
    let module R = (val !r) in let open R in
    match R.deref_head ~depth t with
    | ED.Term.CData c when isc c -> state, cout c, []
    | ED.Term.Const i as t when i < 0 ->
        begin try state, ED.Constants.Map.find i constants, []
        with Not_found -> raise (Conversion.TypeErr(ty,depth,t)) end
    | t -> raise (Conversion.TypeErr(ty,depth,t)) in
  let pp_doc fmt () =
    if doc <> "" then begin
      ED.BuiltInPredicate.pp_comment fmt ("% " ^ doc);
      Format.fprintf fmt "@\n";
    end;
    (* TODO: use typeabbrv *)
    Format.fprintf fmt "@[<hov 2>macro %s :- ctype \"%s\".@]@\n@\n" name c;
    ED.Constants.Map.iter (fun c _ ->
      Format.fprintf fmt "@[<hov 2>type %a %s.@]@\n" ED.Constants.pp c name)
      constants
    in
  { Conversion.embed; readback; ty; pp_doc; pp = (fun fmt x -> pp fmt (cin x)) }

  let conversion_of_cdata ~name ?doc ?(constants=[]) cd =
    let prefix =
      if name = "int" || name = "float" || name = "string" then ""
      else "@" in
    let constants =
      List.fold_right (fun (n,v) ->
        ED.Constants.Map.add (ED.Constants.from_stringc n) v)
        constants ED.Constants.Map.empty in
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

  let int    = RawOpaqueData.conversion_of_cdata ~name:"int"    ED.C.int
  let float  = RawOpaqueData.conversion_of_cdata ~name:"float"  ED.C.float
  let string = RawOpaqueData.conversion_of_cdata ~name:"string" ED.C.string
  let loc    = RawOpaqueData.conversion_of_cdata ~name:"loc"    ED.C.loc
  let poly ty =
    let embed ~depth:_ _ _ state x = state, x, [] in
    let readback ~depth _ _ state t = state, t, [] in
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
    let embed ~depth _ _ state (x,from) =
      let module R = (val !r) in let open R in
      state, R.hmove ~from ~to_:depth ?avoid:None x, [] in
    let readback ~depth _ _ state t =
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

  let list d =
    let embed ~depth h c s l =
      let module R = (val !r) in let open R in
      let s, l, eg = map_acc (d.Conversion.embed ~depth h c) s l in
      s, list_to_lp_list l, eg in
    let readback ~depth h c s t =
      let module R = (val !r) in let open R in
      map_acc (d.Conversion.readback ~depth h c) s
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
  type uvarHandle = Arg of string | Ref of ED.uvar_body
  [@@deriving show]

  type t = {
    handle : uvarHandle;
    lvl : int;
  }

  let pp fmt { handle; lvl } =
    match handle with
    | Arg str ->
        Format.fprintf fmt "%s" str
    | Ref ub ->
        Pp.term fmt (ED.mkUVar ub lvl 0)

  let show m = Format.asprintf "%a" pp m

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
    | Arg s -> { k with handle = Ref (Util.StrMap.find s args) }

  (* This is to hide to the client the fact that Args change representation
      after compilation *)
  let uvk = ED.State.declare ~name:"elpi:uvk" ~pp:(Util.StrMap.pp pp)
    ~clause_compilation_is_over:(fun x -> Util.StrMap.empty)
    ~goal_compilation_is_over:(fun ~args x ->
        Some (Util.StrMap.map (compilation_is_over ~args) x))
    ~init:(fun () -> Util.StrMap.empty)

  let fresh_name =
    let i = ref 0 in
    fun () -> incr i; Printf.sprintf "_uvk_%d_" !i
  
  let alloc_Elpi name lvl state =            
    if ED.State.get Compiler.while_compiling state then
      let state, _arg = Compiler.mk_Arg ~name ~args:[] state in
      state, { lvl; handle = Arg name }
    else
      state, { lvl; handle = Ref (ED.oref ED.Constants.dummy) }

  let make ?name ~lvl state =
    match name with
    | None -> alloc_Elpi (fresh_name ()) lvl state
    | Some name ->
        try state, Util.StrMap.find name (ED.State.get uvk state) 
        with Not_found ->
          let state, k = alloc_Elpi name lvl state in
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
    | Discard                             (* _  *)
    (* FFI *)
    | Builtin of builtin * term list      (* call to a built-in predicate *)
    | CData of RawOpaqueData.t                    (* external data *)
    (* Unassigned unification variables *)
    | UnifVar of Elpi.t * term list

  let look ~depth t =
    let module R = (val !r) in let open R in
    match R.deref_head ~depth t with
    | ED.Term.Arg _ | ED.Term.AppArg _ -> assert false
    | ED.Term.UVar(ub,lvl,nargs) ->
        let args = ED.Term.Constants.mkinterval 0 nargs 0 in
        UnifVar ({ lvl; handle = Ref ub},args)
    | ED.Term.AppUVar(ub,lvl,args) ->
        UnifVar ({ lvl; handle = Ref ub},args)
    | x -> Obj.magic x (* HACK: view is a "subtype" of Term.term *)

  let kool = function
    | UnifVar({ lvl; handle = Ref ub},args) -> ED.Term.AppUVar(ub,lvl,args)
    | UnifVar({ lvl; handle = Arg _},_) -> assert false
    | x -> Obj.magic x
  [@@ inline]

  let mkConst = ED.Term.mkConst
  let mkLam = ED.Term.mkLam
  let mkApp = ED.Term.mkApp
  let mkCons = ED.Term.mkCons
  let mkNil = ED.Term.mkNil
  let mkDiscard = ED.Term.mkDiscard
  let mkBuiltin = ED.Term.mkBuiltin
  let mkCData = ED.Term.mkCData
  let mkAppL = ED.Term.mkAppL
  let mkAppS = ED.Term.mkAppS
  let mkAppSL = ED.Term.mkAppSL
  
  let mkGlobalS s = ED.Term.Constants.from_string s
  let mkBuiltinS s args = mkBuiltin (ED.BuiltInPredicate.from_builtin_name s) args

  let mkGlobal i =
    if i >= 0 then Util.anomaly "mkGlobal: got a bound variable";
    mkConst i
  let mkBound i =
    if i < 0 then Util.anomaly "mkBound: got a global constant";
    mkConst i

  module Constants = ED.Term.Constants

  let of_term = ED.of_term

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

  type constraints = Data.constraints
  
  let constraints = Util.map_filter (function
    | { ED.kind = Constraint { cdepth; conclusion; context } } ->
        Some { context ; goal = (cdepth, conclusion) }
    | _ -> None)
  let no_constraints = []

  let mkUnifVar { Elpi.handle; lvl } ~args state =
  match handle with
  | Elpi.Ref ub -> ED.Term.mkAppUVar ub lvl args
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
        | Elpi.Ref { ED.Term.contents = ub }
          when ub != ED.Term.Constants.dummy ->
            Some (lvl, R.deref_head ~depth:lvl ub)
        | Elpi.Ref _ -> None
        | Elpi.Arg _ -> None in
      H2E.fold (fun k ({Elpi.lvl; handle} as uk) acc -> f k uk (get_val uk) acc) h2e acc

    let uvn = incr uvmap_no; !uvmap_no

    let pp fmt (m : t) =
      let pp k uv _ () =
           Format.fprintf fmt "@[<h>%a@ <-> %a@]" T.pp k Elpi.pp uv
        in
      Format.fprintf fmt "@[<v>";
      fold pp m ();
      Format.fprintf fmt "@]"
    ;;
    
    let show m = Format.asprintf "%a" pp m

    let uvmap = ED.State.declare ~name:(Printf.sprintf "elpi:uvm:%d" uvn) ~pp
      ~clause_compilation_is_over:(fun x -> empty)
      ~goal_compilation_is_over:(fun ~args { h2e; e2h_compile; e2h_run } ->
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
          state, (k,[]), []
      | RawData.UnifVar(k,args) ->
          state, (k,args), []
      | _ -> raise (Conversion.TypeErr (TyName "uvar",depth,t)));
  }

end

module AlgebraicData = struct
  type name = string
  type doc = string

  include ED.BuiltInPredicate.ADT
  let declare x = 
    let look ~depth t =
      let module R = (val !r) in
      R.deref_head ~depth t in
    ED.BuiltInPredicate.adt
      ~look ~alloc:FlexibleData.Elpi.make ~mkUnifVar:RawData.mkUnifVar x
end

module BuiltInPredicate = struct
  include ED.BuiltInPredicate
  exception No_clause = ED.No_clause

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
end

module Query = struct
  include ED.Query
  let compile = Compiler.query_of_data
end

module State = struct
  include ED.State
  (* From now on, we pretend there is no difference between terms at
     compilation time and terms at execution time (in the API) *)
  let declare ~name ~pp ~init =
    declare ~name ~pp ~init
      ~clause_compilation_is_over:(fun x -> x)
      ~goal_compilation_is_over:(fun ~args:_ x -> Some x)
end


module RawQuery = struct
  let mk_Arg = Compiler.mk_Arg
  let is_Arg = Compiler.is_Arg
  let compile = Compiler.query_of_term
end

module Quotation = struct
  include Compiler
  let declare_backtick ~name f =
    ED.CustomFunctorCompilation.declare_backtick_compilation name
      (fun s x -> f s (EA.Func.show x))

  let declare_singlequote ~name f =
    ED.CustomFunctorCompilation.declare_singlequote_compilation name
      (fun s x -> f s (EA.Func.show x))

  let term_at ~depth x = Compiler.term_of_ast ~depth x

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
    | Elpi.Ref { ED.contents = r } ->
        if r == ED.Constants.dummy then None
        else Some r

  let move ~from ~to_ t =
    let module R = (val !r) in let open R in
    R.hmove ~from ~to_ ?avoid:None t
  
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
          Term.mkCon (Data.Constants.show i)
      | Data.Const i -> Util.IntMap.find i ctx
      | Data.Lam t ->
          let s = "x" ^ string_of_int d in
          let ctx = Util.IntMap.add d (Term.mkCon s) ctx in
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
      body = aux depth Util.IntMap.empty term;
    }]

  let map_acc = BuiltInData.map_acc

end

module RawPp = struct
  let term depth fmt t =
    let module R = (val !r) in let open R in
    R.Pp.uppterm depth [] 0 ED.empty_env fmt t

  let constraint_ f c = 
    let module R = (val !r) in let open R in
    R.pp_stuck_goal f c

  let list = Util.pplist

  module Debug = struct
    let term depth fmt t =
      let module R = (val !r) in let open R in
      R.Pp.ppterm depth [] 0 ED.empty_env fmt t
    let show_term = ED.show_term
  end
end
