(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module Data = Elpi_data
module NormalRuntime = Elpi_runtime_trace_off.Elpi_runtime
module TracedRuntime = Elpi_runtime_trace_on.Elpi_runtime

let r = ref (module NormalRuntime : Data.Runtime)

let set_runtime = function
  | true  -> r := (module TracedRuntime : Data.Runtime)
  | false -> r := (module NormalRuntime : Data.Runtime)

let set_trace argv =
  let args = Elpi_trace.parse_argv argv in
  set_runtime !Elpi_trace.debug;
  args

let init argv =
  let new_argv = set_trace argv in
  let new_argv, paths =
    let rec aux args paths = function
      | [] -> List.rev args, List.rev paths
      | "-I" :: p :: rest -> aux args (p :: paths) rest
      | x :: rest -> aux (x :: args) paths rest
    in
      aux [] [] new_argv
  in
  Elpi_parser.init paths;
  new_argv

let trace args = assert(set_trace args = [])

let usage =
  "\nParsing options:\n" ^
  "\t-I PATH  search for accumulated files in PATH\n" ^
  Elpi_trace.usage 

module Runtime = struct

 let query_of_ast p t =
   let module R = (val !r) in let open R in
   query_of_ast p t

 let program_of_ast ?print dl =
   let module R = (val !r) in let open R in
   program_of_ast ?print dl

 let execute_once ~print_constraints p q =
   let module R = (val !r) in let open R in
   execute_once ~print_constraints p q     
        
 let execute_loop p q =
   let module R = (val !r) in let open R in
   execute_loop p q

 let lp_list_to_list ~depth t =
   let module R = (val !r) in let open R in
   lp_list_to_list ~depth t
         
 let list_to_lp_list tl =
   let module R = (val !r) in let open R in
   list_to_lp_list tl

 let query_of_ast_cmap depth cmap ast =
   let module R = (val !r) in let open R in
   query_of_ast_cmap depth cmap ast

 let split_conj t =
   let module R = (val !r) in let open R in
   split_conj t

 let enable_typechecking () =
   let module R = (val !r) in let open R in
   enable_typechecking ()

 let llam_unify da e db a b =
   let module R = (val !r) in let open R in
   llam_unify da e db a b

 let term_of_ast ~depth t =
   let module R = (val !r) in let open R in 
   term_of_ast ~depth t

 let deref_uv ?avoid ~from ~to_ nargs t =
   let module R = (val !r) in let open R in
   deref_uv ?avoid ~from ~to_ nargs t

 let deref_appuv ?avoid ~from ~to_:constant args t =
   let module R = (val !r) in let open R in
   deref_appuv ?avoid ~from ~to_:constant args t

 let is_flex t =
   let module R = (val !r) in let open R in
   is_flex t

 let print_delayed () =
   let module R = (val !r) in let open R in
   print_delayed ()

 type idx = Obj.t (* HACK *)

 let delay_goal ~depth idx ~goal ~on =
   let module R = (val !r) in let open R in
   delay_goal ~depth (Obj.magic idx) ~goal ~on

 let declare_constraint ~depth idx ~goal ~on:term_attributed_ref =
   let module R = (val !r) in let open R in
   declare_constraint ~depth (Obj.magic idx) ~goal ~on:term_attributed_ref

 let register_custom name f =
   NormalRuntime.register_custom name (Obj.magic f);
   TracedRuntime.register_custom name (Obj.magic f)      

end

