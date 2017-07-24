(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
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

let init ?silent argv cwd =
  let new_argv = set_trace argv in
  let new_argv, paths =
    let rec aux args paths = function
      | [] -> List.rev args, List.rev paths
      | "-I" :: p :: rest -> aux args (p :: paths) rest
      | x :: rest -> aux (x :: args) paths rest
    in
      aux [] [] new_argv
  in
  Elpi_parser.init ?silent ~paths ~cwd;
  new_argv

let trace args = assert(set_trace args = [])

let usage =
  "\nParsing options:\n" ^
  "\t-I PATH  search for accumulated files in PATH\n" ^
  Elpi_trace.usage 

let set_warn = Elpi_util.set_warn
let set_error = Elpi_util.set_error
let set_anomaly = Elpi_util.set_anomaly
let set_type_error = Elpi_util.set_type_error

end

module Ast = struct
  type program = Elpi_ast.program
  type query = Elpi_ast.goal
end

module Parse = struct
  let program = Elpi_parser.parse_program
  let goal = Elpi_parser.parse_goal
  let goal_from_stream = Elpi_parser.parse_goal_from_stream
end

module Data = struct
  type program = Elpi_data.program
  type query = Elpi_data.query
  type term = Elpi_data.term

  type constraints = Elpi_data.constraints
  type custom_constraints = Elpi_data.custom_constraints
  type constraint_store = Elpi_data.constraint_store = {
    constraints : constraints;
    custom_constraints : custom_constraints;
  }
  type solution = (string * term) list * constraint_store
end

module Compile = struct

  let program ?print l = Elpi_compiler.program_of_ast ?print (List.flatten l)
  let query = Elpi_compiler.query_of_ast

  let static_check = Elpi_compiler.typecheck

end

module Execute = struct
  type outcome = Elpi_data.outcome =
    Success of Data.solution | Failure | NoMoreSteps
  let once ?max_steps p q = 
    let module R = (val !r) in let open R in
    execute_once ?max_steps p q     
  let loop p q ~more ~pp =
    let module R = (val !r) in let open R in
    execute_loop p q ~more ~pp

end

module Pp = struct
  let term f t = (* XXX query depth *)
    let module R = (val !r) in let open R in
    R.Pp.uppterm 0 [] 0 [||] f t

  let constraints f c =
    let module R = (val !r) in let open R in
    Elpi_util.pplist ~boxed:true R.pp_stuck_goal_kind " " f c

  let custom_constraints = Elpi_data.CustomConstraints.pp

  module Ast = struct
    let program = Elpi_ast.pp_program
  end
end

(****************************************************************************)

module Extend = struct

  module CData = Elpi_util.CData

  module Ast = struct
    include Elpi_ast
    let query_of_term x = Ploc.dummy, x
    let term_of_query (_,x) = x
  end

  module Data = Elpi_data

  module Compile = struct
    module ExtState = Elpi_util.ExtState
    include Elpi_compiler
    let term_at = term_of_ast
  end

  module CustomPredicate = struct
    exception No_clause = Elpi_data.No_clause
    type scheduler = Elpi_data.scheduler =  {
      delay : [ `Goal | `Constraint ] ->
              goal:Data.term -> on:Data.term_attributed_ref list -> unit;
      print : [ `All | `Constraints ] -> Format.formatter -> unit;
    }
    let declare = Elpi_data.register_custom
    let declare_full = Elpi_data.register_custom_full
  end

  module CustomConstraint = struct
    type 'a constraint_type = 'a Elpi_data.CustomConstraints.constraint_type
    let declare = Elpi_data.CustomConstraints.declare_constraint
    let read = Elpi_data.CustomConstraints.read
    let update = Elpi_data.CustomConstraints.update
  end

  module Utils = struct
    let lp_list_to_list ~depth t =
      let module R = (val !r) in let open R in
      lp_list_to_list ~depth t
            
    let list_to_lp_list tl =
      let module R = (val !r) in let open R in
      list_to_lp_list tl
   
    let deref_uv ~from ~to_ ~ano:nargs t =
      let module R = (val !r) in let open R in
      deref_uv ~from ~to_ nargs t

    let deref_appuv ~from ~to_:constant ~args t =
      let module R = (val !r) in let open R in
      deref_appuv ~from ~to_:constant args t

    let rec deref_head on_arg ~depth = function
      | Data.UVar ({ Data.contents = t }, from, ano)
        when t != Data.Constants.dummy ->
         deref_head on_arg ~depth (deref_uv ~from ~to_:depth ~ano t)
      | Data.AppUVar ({Data.contents = t}, from, args)
        when t != Data.Constants.dummy ->
         deref_head on_arg ~depth (deref_appuv ~from ~to_:depth ~args t)
      | Data.App(c,x,xs) when not on_arg ->
         Data.App(c,deref_head true ~depth x,List.map (deref_head true ~depth) xs)
      | x -> x

    let deref_head ~depth t = deref_head false ~depth t
   
    let is_flex ~depth t =
      let module R = (val !r) in let open R in
      is_flex ~depth t

    let error = Elpi_util.error
    let type_error = Elpi_util.type_error
    let anomaly = Elpi_util.anomaly
    let warn = Elpi_util.warn
  end

  module Pp = struct

    let term ?min_prec a b c d e f =
      let module R = (val !r) in let open R in
      R.Pp.uppterm ?min_prec a b c d e f

    let constraint_ f c = 
      let module R = (val !r) in let open R in
      R.pp_stuck_goal_kind f c

    let list = Elpi_util.pplist

    module Raw = struct
      let term ?min_prec a b c d e f =
        let module R = (val !r) in let open R in
        R.Pp.ppterm ?min_prec a b c d e f
      let show_term = Elpi_data.show_term
    end
  end
(*

 let split_conj t =
   let module R = (val !r) in let open R in
   split_conj t

 let llam_unify da e db a b =
   let module R = (val !r) in let open R in
   llam_unify da e db a b
 let print_delayed () =
   let module R = (val !r) in let open R in
   print_delayed ()
 let print_constraints () =
   let module R = (val !r) in let open R in
   print_constraints ()
 let pp_stuck_goal_kind fmt gk =
   let module R = (val !r) in let open R in
   pp_stuck_goal_kind fmt gk

 type idx = Obj.t (* HACK *)

 let delay_goal ~depth idx ~goal ~on =
   let module R = (val !r) in let open R in
   delay_goal ~depth (Obj.magic idx) ~goal ~on

 let declare_constraint ~depth idx ~goal ~on:term_attributed_ref =
   let module R = (val !r) in let open R in
   declare_constraint ~depth (Obj.magic idx) ~goal ~on:term_attributed_ref

 let register_custom name f =
   Elpi_Data.register_custom name (Obj.magic f)

 type 'a constraint_type = 'a Data.CustomConstraints.constraint_type

 let declare_custom_constraint ~name ~pp ~empty =
   Data.CustomConstraints.declare_constraint ~name ~pp ~empty

 let update_custom_constraint = Data.CustomConstraints.update
 let read_custom_constraint = Data.CustomConstraints.read
 
 let get_custom_constraints () =
   let module R = (val !r) in let open R in
   R.get_custom_constraints ()

 let set_custom_constraints cs =
   let module R = (val !r) in let open R in
   R.set_custom_constraints cs
*)

end
