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

let run_prog prog query =
 let query = Runtime.query_of_ast query in
 let prog = Runtime.program_of_ast prog in
 Runtime.execute_loop prog query
;;

let test_impl prog query =
 let query = Runtime.query_of_ast query in
 let prog = Runtime.program_of_ast prog in
 let time f p q =
   let t0 = Unix.gettimeofday () in
   let b = f p q in
   let t1 = Unix.gettimeofday () in
   Printf.printf "TIME: %5.3f\n%!" (t1 -. t0);
   b in
 if time Runtime.execute_once prog query then exit 1 else exit 0
;;


(* rewrites a lambda-prolog program to first-order prolog *)
let pp_lambda_to_prolog prog =
 Printf.printf "\nRewriting λ-prolog to first-order prolog...\n\n%!";
 Runtime.pp_prolog prog
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
   if argv.(1) = "-test" then 2,`OneBatch
   else if argv.(1) = "-prolog" then 2,`PPprologBatch
   else 1,`OneInteractive in
  let filenames = ref [] in
  for i=j to argn - 1 do filenames := argv.(i)::!filenames done;
  let p = Parser.parse_program (List.rev !filenames) in
  let g =
    match test with
    | `OneBatch | `PPprologBatch -> "main."
    | _ ->
    Printf.printf "goal> %!";
    input_line stdin in
  let g = Parser.parse_goal g in
  set_terminal_width ();
  match test with
  | `OneBatch -> test_impl p g
  | `OneInteractive -> run_prog p g
  | `PPprologBatch -> pp_lambda_to_prolog p  
;;
