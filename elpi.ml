let implementations = [ Runtime.impl ]

(*
let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.minor_heap_size = 33554432; (** 4M *)
    Gc.space_overhead = 120;
  } in
  Gc.set tweaked_control
;;
*)

let run_prog impl prog query =
 let (module Impl : Parser.Implementation) =
  List.nth implementations (impl-1) in
 let query = Impl.query_of_ast query in
 let prog = Impl.program_of_ast prog in
 prerr_endline (Impl.msg query);
 Impl.execute_loop prog query
;;

let test_impl impl prog query =
 let (module Impl : Parser.Implementation) =
  List.nth implementations (impl-1) in
 let query = Impl.query_of_ast query in
 let prog = Impl.program_of_ast prog in
 let time f p q =
   let t0 = Unix.gettimeofday () in
   let b = f p q in
   let t1 = Unix.gettimeofday () in
   Printf.printf "TIME: %5.3f\n%!" (t1 -. t0);
   b in
 if time Impl.execute_once prog query then exit 1 else exit 0
;;


let print_implementations () =
 List.iteri (
  fun i (module Impl : Parser.Implementation) ->
   prerr_string ("Implementation #" ^ string_of_int (i+1) ^ ": ");
   prerr_endline (Impl.msg (Impl.query_of_ast (Parser.Const Parser.ASTFuncS.truef))) ;
 ) implementations
;;

(* rewrites a lambda-prolog program to first-order prolog *)
let pp_lambda_to_prolog impl prog =
 let (module Impl : Parser.Implementation) =
  List.nth implementations (impl - 1) in
 Printf.printf "\nRewriting λ-prolog to first-order prolog...\n\n%!";
 Impl.pp_prolog prog
;;

let set_terminal_width ?(max_w=
    let ic, _ as p = Unix.open_process "tput cols" in
    let w = int_of_string (input_line ic) in
    let _ = Unix.close_process p in w) () =
  Format.pp_set_margin Format.err_formatter max_w;
  Format.pp_set_ellipsis_text Format.err_formatter "...";
  Format.pp_set_max_boxes Format.err_formatter 30;
;;

let _ =
  let argv = Sys.argv in
  let argn = Array.length argv in
  (* j=1 iff -test is not passed *)
  let j,test =
   if argv.(1) = "-test" then
     if argn = 4 then 3,`OneBatch (int_of_string (argv.(2)))
     else 2,`OneBatch 1
   else if argv.(1) = "-prolog" then 3,`PPprologBatch (int_of_string (argv.(2)))
   else if argv.(1) = "-impl" then 2,`OneInteractive (1)
   else if argv.(1) = "-list" then
    (print_implementations (); exit 0)
   else 1,`OneInteractive 1 in
  let filenames = ref [] in
  for i=j to argn - 1 do filenames := argv.(i)::!filenames done;
  let p = Parser.parse_program (List.rev !filenames) in
  let g =
    match test with
    | `OneBatch _ | `PPprologBatch _ -> "main."
    | _ ->
    Printf.printf "goal> %!";
    input_line stdin in
  let g = Parser.parse_goal g in
  set_terminal_width ();
  match test with
  | `OneBatch impl -> test_impl impl p g
  | `OneInteractive impl -> run_prog impl p g
  | `PPprologBatch impl -> pp_lambda_to_prolog impl p  
;;
