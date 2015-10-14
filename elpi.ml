(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

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
 Gc.compact ();
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
  List.iter (fun fmt ->
    Format.pp_set_margin fmt max_w;
    Format.pp_set_ellipsis_text fmt "...";
    Format.pp_set_max_boxes fmt 30)
  [ Format.err_formatter; Format.std_formatter ]
;;

let _ =
  let argv = Trace.parse_argv Sys.argv in
  let argn = Array.length argv in
  (* j=1 iff -test is not passed *)
  let j,test =
   if Array.length argv = 1 then 1,`OneInteractive
   else if argv.(1) = "-test" then 2,`OneBatch
   else if argv.(1) = "-prolog" then 2,`PPprologBatch
   else if argv.(1) = "-latex_export" then 2,`LatexExport
   else 1,`OneInteractive in
  let filenames = ref [] in
  for i=j to argn - 1 do filenames := argv.(i)::!filenames done;
  let p = Parser.parse_program (List.rev !filenames) in
  let g =
    match test with
    | `OneBatch | `LatexExport | `PPprologBatch -> "main."
    | _ ->
    Printf.printf "goal> %!";
    input_line stdin in
  let g = Parser.parse_goal g in
  set_terminal_width ();
  match test with
  | `OneBatch -> test_impl p g
  | `OneInteractive -> run_prog p g
  | `PPprologBatch -> pp_lambda_to_prolog p  
  | `LatexExport ->
      (* the program in the .elpi file(s) of the user only, 
         without pervasives.elpi; mostly for LaTeX exporting purposes*)
      let my_p = Parser.reparse_program (List.rev !filenames) in 
       Latex_exporter.Export.export_clauses my_p
;;
