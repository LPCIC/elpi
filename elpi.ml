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

let pr_constraints cs =
  if cs <> [] then begin
  Format.eprintf "\nConstraints:\n%a\n%!"
    (Elpi_util.pplist Elpi_API.Runtime.pp_stuck_goal_kind " " ~boxed:true)
    cs
end

let print_solution time = function
| `NoMoreSteps -> Format.eprintf "Interrupted (no more steps)\n%!"
| `Failure -> Format.eprintf "Failure\n%!"
| `Success (s,cs) ->
  Format.eprintf "\nSuccess:\n%!" ;
  Elpi_API.Data.SMap.iter (fun name t ->
    Format.eprintf "  @[<hov 1>%s = %a@]\n%!" name
      (Elpi_API.Pp.uppterm 0 [] 0 [||]) t) s;
  Format.eprintf "\nTime: %5.3f\n%!" time;
  pr_constraints cs.Elpi_API.Data.constraints;
  Format.eprintf "\nRaw result: \n%!" ;
  Elpi_API.Data.SMap.iter (fun name t ->
    Format.eprintf "  @[<hov 1>%s = %a@]\n%!" name
      (Elpi_API.Pp.ppterm 0 [] 0 [||]) t) s;
;;
  
let more () =
  prerr_endline "\nMore? (Y/n)";
  read_line() <> "n"
;;

let run_prog typecheck prog query =
 let prog = Elpi_API.Compiler.program_of_ast prog in
 let query = Elpi_API.Compiler.query_of_ast prog query in
 if typecheck then Elpi_API.Compiler.typecheck prog query;
 Elpi_API.Runtime.execute_loop prog query ~more ~pp:print_solution
;;

let test_impl typecheck prog query =
 let prog = Elpi_API.Compiler.program_of_ast prog in
 let query = Elpi_API.Compiler.query_of_ast prog query in
 if typecheck then Elpi_API.Compiler.typecheck prog query;
 Gc.compact ();
 let time f p q =
   let t0 = Unix.gettimeofday () in
   let b = f p q in
   let t1 = Unix.gettimeofday () in
   match b with `Success _ -> print_solution (t1 -. t0) b; true | _ -> false in
 if time Elpi_API.Runtime.execute_once prog query then exit 0 else exit 1
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
  "\nUsage: elpi [OPTION].. [FILE].. [-- ARGS..] \n" ^ 
  "\nMain options:\n" ^ 
  "\t-test runs the query \"main\"\n" ^ 
  "\t-exec pred  runs the query \"pred args\"\n" ^ 
  "\t-print-prolog prints files to Prolog syntax if possible, then exit\n" ^ 
  "\t-print-latex prints files to LaTeX syntax, then exit\n" ^ 
  "\t-print prints files after desugar, then exit\n" ^ 
  "\t-print-raw prints files after desugar in ppx format, then exit\n" ^ 
  "\t-print-ast prints files as parsed, then exit\n" ^ 
  "\t-I path searches files in path\n" ^ 
  Elpi_API.usage
;;

let _ =
  let test = ref false in
  let exec = ref "" in
  let args = ref [] in
  let print_prolog = ref false in
  let print_latex = ref false in
  let print_lprolog = ref None in
  let print_ast = ref false in
  let typecheck = ref true in
  let batch = ref false in
  let rec aux = function
    | [] -> []
    | "-test" :: rest -> batch := true; test := true; aux rest
    | "-exec" :: goal :: rest ->  batch := true; exec := goal; aux rest
    | "-print-prolog" :: rest -> print_prolog := true; aux rest
    | "-print-latex" :: rest -> print_latex := true; aux rest
    | "-print" :: rest -> print_lprolog := Some `Yes; aux rest
    | "-print-raw" :: rest -> print_lprolog := Some `Raw; aux rest
    | "-print-ast" :: rest -> print_ast := true; aux rest
    | "-no-tc" :: rest -> typecheck := false; aux rest
    | ("-h" | "--help") :: _ -> Printf.eprintf "%s" usage; exit 0
    | "--" :: rest -> args := rest; []
    | s :: _ when String.length s > 0 && s.[0] == '-' ->
        Printf.eprintf "Unrecognized option: %s\n%s" s usage; exit 1
    | x :: rest -> x :: aux rest in
  let cwd = Unix.getcwd () in
  let tjpath =
    let v = try Sys.getenv "TJPATH" with Not_found -> "" in
    let tjpath = Str.split (Str.regexp ":") v in
    List.flatten (List.map (fun x -> ["-I";x]) tjpath) in
  let execpath =
    try ["-I"; Filename.dirname (Unix.readlink "/proc/self/exe")]
    with Unix.Unix_error _ -> [ "-I"; "." ] in
  let opts = Array.to_list Sys.argv @ tjpath @ execpath in
  let argv = Elpi_API.init ~silent:false opts cwd in
  let filenames = aux (List.tl argv) in
  set_terminal_width ();
  if !print_latex then Elpi_latex_exporter.activate () ;
  let p = Elpi_parser.parse_program filenames in
  if !print_ast then begin
    Format.eprintf "%a" Elpi_ast.pp_program p;
    exit 0;
  end;
  if !print_latex then exit 0;
  if !print_prolog then (pp_lambda_to_prolog p; exit 0);
  if !print_lprolog != None then begin
    Format.eprintf "@[<v>";
    let _ = Elpi_API.Compiler.program_of_ast ?print:!print_lprolog p in
    Format.eprintf "@]%!";
    exit 0;
    end;
  let g =
   if !test then Elpi_parser.parse_goal "main."
   else if !exec <> "" then
     begin Elpi_parser.parse_goal
       (Printf.sprintf "%s [%s]." !exec
         String.(concat ", " (List.map (Printf.sprintf "\"%s\"") !args)))
        end
   else begin
    Printf.printf "goal> %!";
    let strm = Stream.of_channel stdin in
    Elpi_parser.parse_goal_from_stream strm
   end in
  if !batch then test_impl !typecheck p g
  else run_prog !typecheck p g
;;
