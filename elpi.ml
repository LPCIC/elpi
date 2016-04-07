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
 let prog = Elpi_runtime.program_of_ast prog in
 let query = Elpi_runtime.query_of_ast prog query in
 Elpi_runtime.execute_loop prog query
;;

let test_impl prog query =
 let prog = Elpi_runtime.program_of_ast prog in
 let query = Elpi_runtime.query_of_ast prog query in
 Gc.compact ();
 let time f p q =
   let t0 = Unix.gettimeofday () in
   let b = f p q in
   let t1 = Unix.gettimeofday () in
   Printf.printf "TIME: %5.3f\n%!" (t1 -. t0);
   b in
 if time Elpi_runtime.execute_once prog query then exit 1 else exit 0
;;


(* rewrites a lambda-prolog program to first-order prolog *)
let pp_lambda_to_prolog prog =
 Printf.printf "\nRewriting λ-prolog to first-order prolog...\n\n%!";
 Elpi_prolog_exporter.pp_prolog prog
;;

let set_terminal_width ?(max_w=
    let ic, _ as p = Unix.open_process "tput cols" in
    let w = int_of_string (input_line ic) in
    let _ = Unix.close_process p in w) () =
  List.iter (fun fmt ->
    Format.pp_set_margin fmt max_w;
    Format.pp_set_ellipsis_text fmt "...";
    Format.pp_set_max_boxes fmt 0)
  [ Format.err_formatter; Format.std_formatter ]
;;


let usage () =
  Format.eprintf "\nusage: elpi [OPTIONS]... [FILENAME]...\n";

  Format.eprintf "\nmain options:\n";
  Format.eprintf "\t-test runs the query \"main\"\n";
  Format.eprintf "\t-prolog prints files to Prolog syntax if possible\n";
  Format.eprintf "\t-latex_export prints files to LaTeX syntax\n";

  Elpi_trace.usage ()
;;

let _ =
  let argv = Elpi_trace.parse_argv Sys.argv in
  let argn = Array.length argv in
  if argn = 2 && (argv.(1) = "-h" || argv.(1) = "--help") then
   begin usage () ; exit 0 end;
  (* j=1 iff -test is not passed *)
  let j,test =
   if argn = 1 then 1,`OneInteractive
   else if argv.(1) = "-test" then 2,`OneBatch
   else if argv.(1) = "-prolog" then 2,`PPprologBatch
   else if argv.(1) = "-latex_export" then 2,`LatexExport
   else 1,`OneInteractive in
  let filenames = ref [] in
  for i=j to argn - 1 do filenames := argv.(i)::!filenames done;
  set_terminal_width ();
  if test = `LatexExport then begin
   Elpi_latex_exporter.activate () ;
   ignore (Elpi_parser.parse_program (List.rev !filenames))
  end else
   let p = Elpi_parser.parse_program (List.rev !filenames) in
   let g =
     match test with
     | `OneBatch | `LatexExport | `PPprologBatch ->
       Elpi_parser.parse_goal "main."
     | _ ->
     Printf.printf "goal> %!";
     let strm = Stream.of_channel stdin in
     Elpi_parser.parse_goal_from_stream strm in
   match test with
   | `OneBatch -> test_impl p g
   | `OneInteractive -> run_prog p g
   | `PPprologBatch -> pp_lambda_to_prolog p  
   | `LatexExport -> ()
;;
