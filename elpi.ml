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


let usage =
  "\nusage: elpi [OPTION].. [FILE]..\n" ^ 
  "\nmain options:\n" ^ 
  "\t-test runs the query \"main\"\n" ^ 
  "\t-print-prolog prints files to Prolog syntax if possible, then exit\n" ^ 
  "\t-print-latex prints files to LaTeX syntax, then exit\n" ^ 
  "\t-print prints files after desugar, then exit\n" ^ 
  "\t-print-raw prints files after desugar in ppx format, then exit\n" ^ 
  "\t-print-ast prints files as parsed, then exit\n" ^ 
  Elpi_trace.usage
;;

let _ =
  let test = ref false in
  let print_prolog = ref false in
  let print_latex = ref false in
  let print_lprolog = ref None in
  let print_ast = ref false in
  let typecheck = ref true in
  let rec aux = function
    | [] -> []
    | "-test" :: rest -> test := true; aux rest
    | "-print-prolog" :: rest -> print_prolog := true; aux rest
    | "-print-latex" :: rest -> print_latex := true; aux rest
    | "-print" :: rest -> print_lprolog := Some `Yes; aux rest
    | "-print-raw" :: rest -> print_lprolog := Some `Raw; aux rest
    | "-print-ast" :: rest -> print_ast := true; aux rest
    | "-no-tc" :: rest -> typecheck := false; aux rest
    | ("-h" | "--help") :: _ -> Printf.eprintf "%s" usage; exit 0
    | s :: _ when String.length s > 0 && s.[0] == '-' ->
        Printf.eprintf "Unrecognized option: %s\n%s" s usage; exit 1
    | x :: rest -> x :: aux rest in
  let filenames = aux (List.tl (Array.to_list (Elpi_trace.parse_argv Sys.argv))) in
  set_terminal_width ();
  if !print_latex then Elpi_latex_exporter.activate () ;
  let p = Elpi_parser.parse_program ~paths:[] ~filenames in
  if !print_ast then begin
    Format.eprintf "%a" Elpi_ast.pp_program p;
    exit 0;
  end;
  if !print_latex then exit 0;
  if !print_prolog then (pp_lambda_to_prolog p; exit 0);
  if !print_lprolog != None then begin
    Format.eprintf "@[<v>";
    let _ = Elpi_runtime.program_of_ast ?print:!print_lprolog p in
    Format.eprintf "@]%!";
    exit 0;
    end;
  let g =
   if !test then Elpi_parser.parse_goal "main."
   else begin
    Printf.printf "goal> %!";
    let strm = Stream.of_channel stdin in
    Elpi_parser.parse_goal_from_stream strm
   end in
  if !typecheck then Elpi_runtime.enable_typechecking ();
  if !test then test_impl p g
  else run_prog p g
;;
