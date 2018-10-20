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

type builtins = Elpi_data.Builtin.declaration list
type program_header = Elpi_ast.program

let init ?silent ~builtins ~basedir:cwd argv =
  let new_argv = set_trace argv in
  let new_argv, paths =
    let rec aux args paths = function
      | [] -> List.rev args, List.rev paths
      | "-I" :: p :: rest -> aux args (p :: paths) rest
      | x :: rest -> aux (x :: args) paths rest
    in
      aux [] [] new_argv
  in
  Elpi_parser.init ?silent ~lp_syntax:Elpi_parser.lp_gramext ~paths ~cwd ();
  (* This is a bit ugly, since builtins are global but could be made
   * program specific *)
  List.iter (function
    | Elpi_data.Builtin.MLCode (p,_) -> Elpi_data.Builtin.register p
    | Elpi_data.Builtin.LPCode _ -> ()
    | Elpi_data.Builtin.LPDoc _ -> ()) builtins;
  (* This is a bit ugly, since we print and then parse... *)
  let b = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer b in
  Elpi_data.Builtin.document fmt builtins;
  Format.pp_print_flush fmt ();
  let strm = Stream.of_string (Buffer.contents b) in
  let header = Elpi_parser.parse_program_from_stream strm in
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
  type program = Elpi_ast.program
  type query = Elpi_ast.goal
end

module Parse = struct
  let program = Elpi_parser.parse_program
  let program_from_stream = Elpi_parser.parse_program_from_stream
  let goal = Elpi_parser.parse_goal
  let goal_from_stream = Elpi_parser.parse_goal_from_stream
end

module Data = struct
  type term = Elpi_data.term
  type constraints = Elpi_data.constraints
  type custom_state = Elpi_data.custom_state
  module StrMap = Elpi_util.StrMap
  type solution = Elpi_data.solution = {
    assignments : term StrMap.t;
    constraints : constraints;
    state : custom_state;
  }
end

module Compile = struct

  type program = Elpi_compiler.program
  type query = Elpi_compiler.query
  type executable = Elpi_data.executable

  let program header l = Elpi_compiler.program_of_ast (header @ List.flatten l)
  let query = Elpi_compiler.query_of_ast

  let static_check header ?checker ?flags p =
    let module R = (val !r) in let open R in
    let checker = Elpi_util.option_map List.flatten checker in
    Elpi_compiler.static_check header ~exec:(execute_once ~delay_outside_fragment:false) ?checker ?flags p

  module StrSet = Elpi_util.StrSet

  type flags = Elpi_compiler.flags = {
    defined_variables : StrSet.t;
    allow_untyped_builtin : bool;
  }
  let default_flags = Elpi_compiler.default_flags
  let link ?flags x =
    Elpi_compiler.executable_of_query ?flags x

  let dummy_header = []
end

module Execute = struct
  type outcome = Elpi_data.outcome =
    Success of Data.solution | Failure | NoMoreSteps
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

  let custom_state = Elpi_data.CustomState.pp

  let query f c =
    let module R = (val !r) in let open R in
    Elpi_compiler.pp_query (fun ~depth -> R.Pp.uppterm depth [] 0 [||]) f c

  module Ast = struct
    let program = Elpi_ast.pp_program
  end
end

(****************************************************************************)

module Extend = struct

  module CData = Elpi_util.CData

  module Data = struct
    module StrMap = Data.StrMap
    type builtin = int
    include Elpi_data
    let mkBuiltinName s args = mkBuiltin (Builtin.from_builtin_name s) args
   
    let look ~depth t =
      let module R = (val !r) in let open R in
      R.deref_head ~depth t

    let kool x = x [@@ inline]

    type suspended_goal = { 
      context : hyps;
      goal : int * term
    }
    let constraints = Elpi_util.map_filter (function
      | { kind = Constraint { cdepth; conclusion; context } } ->
          Some { context ; goal = (cdepth, conclusion) }
      | _ -> None)
    let fresh_uvar_body () = oref Constants.dummy
    let of_solution x = x
  end

  module Compile = struct
    module State = Elpi_data.CompilerState
    include Elpi_compiler
    let term_at ~depth (_,x) = term_of_ast ~depth x
    let query = query_of_term
  end

  module BuiltInPredicate = struct
    exception No_clause = Elpi_data.No_clause
    include Elpi_data.Builtin

    let data_of_cdata ~name:ty ?(constants=Data.Constants.Map.empty)
      { CData.cin; isc; cout }
    =
      let to_term ~depth:_ x = Data.CData (cin x) in
      let of_term ~depth t =
        let module R = (val !r) in let open R in
        match R.deref_head ~depth t with
        | Data.CData c when isc c -> Data (cout c)
        | (Data.UVar _ | Data.AppUVar _) as x -> Flex x
        | Data.Discard -> Discard
        | Data.Const i as t when i < 0 ->
            begin try Data (Data.Constants.Map.find i constants)
            with Not_found -> raise (TypeErr t) end
        | t -> raise (TypeErr t) in
      { to_term; of_term; ty }

    let int    = data_of_cdata ~name:"int" Elpi_data.C.int
    let float  = data_of_cdata ~name:"float" Elpi_data.C.float
    let string = data_of_cdata ~name:"string" Elpi_data.C.string
    let poly ty =
      let to_term ~depth:_ x = x in
      let of_term ~depth t =
        let module R = (val !r) in let open R in
        match R.deref_head ~depth t with
        | Data.Discard -> Discard
        | x -> Data x in
      { to_term; of_term; ty }
    let any = poly "any"
    let list d =
      let to_term ~depth l =
        let module R = (val !r) in let open R in
        list_to_lp_list (List.map (d.to_term ~depth) l) in
      let of_term ~depth t =
        let module R = (val !r) in let open R in
        match R.deref_head ~depth t with
        | Data.Discard -> Discard
        | (Data.UVar _ | Data.AppUVar _) as x -> Flex x
        | _ ->
            Data (List.fold_right (fun t l ->
              match d.of_term ~depth t with
              | Data x -> x :: l
              | _ -> raise (TypeErr t))
                (lp_list_to_list ~depth t) []) in
      { to_term; of_term; ty = "list " ^ d.ty }

    let builtin_of_declaration x = x

    module Notation = struct
 
      let (!:) x = (), Some x
      let (+!) a b = a, Some b
      let (?:) x = (), x
      let (+?) a b = a, b

    end
  end

  module CustomState = Elpi_data.CustomState

  module CustomFunctor = struct
  
    let declare_backtick ~name f =
      Elpi_data.CustomFunctorCompilation.declare_backtick_compilation name
        (fun s x -> f s (Elpi_ast.Func.show x))

    let declare_singlequote ~name f =
      Elpi_data.CustomFunctorCompilation.declare_singlequote_compilation name
        (fun s x -> f s (Elpi_ast.Func.show x))

  end

  module Utils = struct
    let lp_list_to_list ~depth t =
      let module R = (val !r) in let open R in
      lp_list_to_list ~depth t
            
    let list_to_lp_list tl =
      let module R = (val !r) in let open R in
      list_to_lp_list tl

    let unsafe_look x = x

    let get_assignment { Elpi_data.contents = r } =
      if r == Elpi_data.Constants.dummy then None
      else Some r

    let move ~from ~to_ t =
      let module R = (val !r) in let open R in
      R.hmove ~from ~to_ ?avoid:None t
   
    let error = Elpi_util.error
    let type_error = Elpi_util.type_error
    let anomaly = Elpi_util.anomaly
    let warn = Elpi_util.warn

    let clause_of_term ?name ?graft ~depth term =
      let module Ast = Elpi_ast in
      let module R = (val !r) in let open R in
      let rec aux d ctx t =
        match R.deref_head ~depth:d t with       
        | Data.Const i when i >= 0 && i < depth ->
            error "program_of_term: the term is not closed"
        | Data.Const i when i < 0 ->
            Ast.mkCon (Data.Constants.show i)
        | Data.Const i -> Elpi_util.IntMap.find i ctx
        | Data.Lam t ->
            let s = "x" ^ string_of_int d in
            let ctx = Elpi_util.IntMap.add d (Ast.mkCon s) ctx in
            Ast.mkLam s (aux (d+1) ctx t)
        | Data.App(c,x,xs) ->
            let c = aux d ctx (Data.Constants.mkConst c) in
            let x = aux d ctx x in
            let xs = List.map (aux d ctx) xs in
            Ast.mkApp (c :: x :: xs)
        | (Data.Arg _ | Data.AppArg _) -> assert false
        | Data.Cons(hd,tl) ->
            let hd = aux d ctx hd in
            let tl = aux d ctx tl in
            Ast.mkSeq [hd;tl]
        | Data.Nil -> Ast.mkNil
        | Data.Builtin(c,xs) ->
            let c = aux d ctx (Data.Constants.mkConst c) in
            let xs = List.map (aux d ctx) xs in
            Ast.mkApp (c :: xs)
        | Data.CData x -> Ast.mkC x
        | (Data.UVar _ | Data.AppUVar _) ->
            error "program_of_term: the term contains uvars"
        | Data.Discard -> Ast.mkCon "_"
      in
      let attributes =
        (match name with Some x -> [Ast.Name x] | None -> []) @
        (match graft with
         | Some (`After,x) -> [Ast.After x]
         | Some (`Before,x) -> [Ast.Before x]
         | None -> []) in
      [Ast.Clause {
        Ast.loc = Ploc.dummy;
        Ast.attributes;
        Ast.body = aux depth Elpi_util.IntMap.empty term;
      }]

  end

  module Pp = struct

    let term depth fmt t =
      let module R = (val !r) in let open R in
      R.Pp.uppterm depth [] 0 Elpi_data.empty_env fmt t

    let constraint_ f c = 
      let module R = (val !r) in let open R in
      R.pp_stuck_goal f c

    let list = Elpi_util.pplist

    module Raw = struct
      let term depth fmt t =
        let module R = (val !r) in let open R in
        R.Pp.ppterm depth [] 0 Elpi_data.empty_env fmt t
      let show_term = Elpi_data.show_term
    end
  end
end

