(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
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
open Elpi

module Str = Re.Str

let print_solution time = function
| API.Execute.NoMoreSteps ->
   Format.eprintf "Interrupted (no more steps)@\n%!"
| API.Execute.Failure -> Format.eprintf "Failure@\n%!"
| API.Execute.Success {
    API.Data.assignments; constraints; state; pp_ctx; _ } ->
  Format.eprintf "@\nSuccess:@\n%!" ;
  API.Data.StrMap.iter (fun name v ->
    Format.eprintf "  @[<hov 1>%s = %a@]@\n%!" name
      (API.Pp.term pp_ctx) v) assignments;
  Format.eprintf "@\nTime: %5.3f@\n%!" time;
  Format.eprintf "@\nConstraints:@\n%a@\n%!"
    (API.Pp.constraints pp_ctx) constraints;
  Format.eprintf "@\nState:@\n%a@\n%!"
    API.Pp.state state;
;;
  
let more () =
  prerr_endline "\nMore? (Y/n)";
  read_line() <> "n"
;;

let set_terminal_width ?(max_w=
   try
    let ic, _, _ as p = Unix.open_process_full "tput cols" (Unix.environment()) in
    let w = int_of_string (input_line ic) in
    let _ = Unix.close_process_full p in w
   with _ -> 80) () =
  List.iter (fun fmt ->
    Format.pp_set_margin fmt max_w;
    Format.pp_set_ellipsis_text fmt "...";
    Format.pp_set_max_boxes fmt 0)
  [ Format.err_formatter; Format.std_formatter ]
;;

let usage =
  "\nUsage: elpi [OPTION].. [FILE] [-- ARGS..] \n" ^ 
  "\nMain options:\n" ^ 
  "\t-test runs the query \"main\"\n" ^ 
  "\t-exec pred  runs the query \"pred ARGS\"\n" ^ 
  "\t-no-det  disable determinacy analysis\n" ^ 
  "\t-max-errors N  report at most N errors (default 5); 0: stop at the first one\n" ^ 
  "\t-D var  Define variable (conditional compilation)\n" ^ 
  "\t-document-builtins Print documentation for built-in predicates\n" ^
  "\t-document-infix-syntax Print the documentation for infix operators\n" ^
  "\t-I PATH  search for accumulated files in PATH\n" ^
  "\t-delay-problems-outside-pattern-fragment (deprecated, for Teyjus\n" ^
  "\t                                          compatibility)\n" ^
  "\t--version prints the version of Elpi (also -v or -version)\n" ^ 
  "\t--help prints this help (also -h or -help)\n" ^ 
 API.Setup.usage ^
  "\nDebug options (for debugging Elpi, not your program):\n" ^ 
  "\t-parse-term parses a term from standard input and prints it\n" ^
  "\t-parse-clause parses a rule from standard input and prints it\n" ^
  "\t-print-ast prints files as parsed, then exit\n" ^
  "\t-print prints files after most compilation passes, then exit\n" ^ 
  "\t-print-units prints compilation units data, then exit\n"
;;

(* the errors that a pass found, sorted by location (the ones without a
   location, e.g. "too many errors", come last); none of them is fatal on its
   own, so they are all labelled in the same way *)
let report errors =
  let key (e : API.Error.t) = match e.loc with
    | None -> None
    | Some l -> Some (l.API.Ast.Loc.source_name, l.API.Ast.Loc.source_start) in
  let cmp a b = match key a, key b with
    | None, None -> 0 | None, _ -> 1 | _, None -> -1
    | Some (f1, s1), Some (f2, s2) ->
        match String.compare f1 f2 with 0 -> Int.compare s1 s2 | c -> c in
  let errors = List.stable_sort cmp errors in
  List.iter (fun (e : API.Error.t) ->
    Format.eprintf "@[<hv>Error: %a@]\n%!" API.Error.pp e)
    errors

(* the warnings that a pass found, in order *)
let report_warnings warnings =
  List.iter (fun { API.Error.warning = e } ->
    Format.eprintf "@[<hv>Warning: %a@]\n%!" API.Error.pp e)
    warnings

(* the compiled query, or its error; the warnings are printed *)
let query_or_exit (q, warnings) =
  report_warnings warnings;
  match q with
  | Ok q -> q
  | Error e -> report [ e ]; exit 1

(* the result of a pass, or the errors it found; the warnings are printed *)
let or_exit (x, errors, warnings) =
  report_warnings warnings;
  report errors;
  if errors <> [] then exit 1;
  x

let read_all ic =
  let b = Buffer.create 1024 in
  (try while true do Buffer.add_channel b ic 1 done with End_of_file -> ());
  Buffer.contents b

(* the errors raised: with -max-errors 0 the first error of a pass, and the
   errors of the builtins at run time *)
let raising f =
  try f ()
  with
  | API.Parse.ParseError (loc, message) ->
      report [ { API.Error.component = "Parser"; loc = Some loc; message } ]; exit 1
  | API.Error.ElpiError e -> report [ e ]; exit 1

(* For testing purposes we declare an identity quotation *)
let quotations = API.Quotation.new_quotations_descriptor ()
let _ =
  API.Quotation.register_named_quotation ~descriptor:quotations ~name:"elpi"
    API.Quotation.elpi

let _ =
  (* Memtrace.trace_if_requested (); <-- new line *)
  (* Hashtbl.randomize (); *)
  let test = ref false in
  let exec = ref "" in
  let print_lprolog = ref false in
  let print_ast = ref false in
  let batch = ref false in
  let doc_builtins = ref false in
  let doc_infix = ref false in
  let delay_outside_fragment = ref false in 
  let print_passes = ref false in
  let print_units = ref false in
  let extra_paths = ref [] in
  let parse_term = ref false in
  let parse_clause = ref false in
  let skip_det_check = ref false in
  let max_errors = ref 5 in
  let print_deps = ref false in
  let vars =
    ref API.Compile.(default_flags.defined_variables) in
  let rec eat_options = function
    | [] -> []
    | "-delay-problems-outside-pattern-fragment" :: rest -> delay_outside_fragment := true; eat_options rest
    | "-test" :: rest -> batch := true; test := true; eat_options rest
    | "-exec" :: goal :: rest ->  batch := true; exec := goal; eat_options rest
    | "-no-det" :: rest -> skip_det_check := true; eat_options rest
    | "-max-errors" :: n :: rest ->
        (match int_of_string_opt n with
         | Some n when n >= 0 -> max_errors := n
         | _ -> Printf.eprintf "-max-errors expects a number (0 or more), not %s\n" n; exit 1);
        eat_options rest
    | "-print" :: rest -> print_lprolog := true; eat_options rest
    | "-print-ast" :: rest -> print_ast := true; eat_options rest
    | "-print-units" :: rest -> print_units := true; eat_options rest
    | "-parse-term" :: rest -> parse_term := true; eat_options rest
    | "-parse-clause" :: rest -> parse_clause := true; eat_options rest
    | "-deps" :: rest -> print_deps := true; eat_options rest
    | "-document-builtins" :: rest -> doc_builtins := true; eat_options rest
    | "-document-infix-syntax" :: rest -> doc_infix := true; eat_options rest
    | "-D" :: var :: rest -> vars := API.Compile.StrSet.add var !vars; eat_options rest
    | "-I" :: p :: rest -> extra_paths := !extra_paths @ [p]; eat_options rest
    | ("-h" | "--help" | "-help") :: _ -> Printf.eprintf "%s" usage; exit 0
    | ("-v" | "--version" | "-version") :: _ -> Printf.printf "%s\n" "%%VERSION_NUM%%"; exit 0
    | "--" :: rest -> "--" :: rest
    | x :: rest -> x :: eat_options rest
  in
  let tjpath =
    let v = try Sys.getenv "TJPATH" with Not_found -> "" in
    Str.split (Str.regexp ":") v in
  let installpath = 
    let v = try Sys.getenv "OCAMLPATH" with Not_found -> "" in
    (Filename.dirname Sys.executable_name ^ "/../lib/") ::
    (Filename.dirname Sys.executable_name ^ "/../lib/ocaml") ::
    Str.split (Str.regexp ":") v in
  let execpath = Filename.dirname (Sys.executable_name) in
  let argv = List.tl (Array.to_list Sys.argv) in
  let argv = eat_options argv in
  let paths = tjpath @ installpath @ [execpath] @ !extra_paths in
  let flags = {
      API.Compile.defined_variables = !vars;
      API.Compile.print_units = !print_units;
      API.Compile.time_typechecking = true;
      API.Compile.skip_det_checking = !skip_det_check;
      API.Compile.max_errors = !max_errors;
  } in
  if !doc_infix then begin
    Printf.eprintf "%s" Elpi_parser.Parser_config.legacy_parser_compat_error;
    exit 0
  end;
  let elpi =
    API.Setup.init
      ~quotations
      ~flags:(API.Compile.to_setup_flags flags)
      ~builtins:[Builtin.std_builtins]
      ~file_resolver:(API.Parse.std_resolver ~paths ())
      () in
  if !parse_term then begin
    let g = query_or_exit (API.Parse.query_from ~elpi ~loc:(API.Ast.Loc.initial "(-parse-term)") (Lexing.from_channel stdin)) in
    Format.printf "Raw term: %a\n" API.Pp.Ast.query g;
    let p = raising (fun () -> or_exit (API.Parse.program_from ~flags ~elpi ~loc:(API.Ast.Loc.initial "(parse_term)") ~digest:(Digest.string "")  (Lexing.from_string ""))) in
    let prog = raising (fun () -> or_exit (API.Compile.program ~flags ~elpi p)) in
    let query = query_or_exit (API.Compile.query prog g) in
    Format.printf "Compiled term: %a\n" API.Pp.goal query;
    exit 0;
  end;
  if !parse_clause then begin
    let p = raising (fun () -> or_exit (API.Parse.program_from ~flags ~elpi ~loc:(API.Ast.Loc.initial "(-parse-clause)") ~digest:(Digest.string "") (Lexing.from_string (read_all stdin)))) in
    Format.printf "Raw clause: %a\n" API.Pp.Ast.program p;
    exit 0;
  end;
  let argv = API.Setup.trace argv in
  let rec eat_filenames acc = function
    | [] -> List.rev acc, []
    | "--" :: rest -> List.rev acc, rest
    | s :: _ when String.length s > 0 && s.[0] == '-' ->
        Printf.eprintf "Unrecognized option: %s\n%s" s usage; exit 1
    | x :: rest -> eat_filenames (x::acc) rest in
  let files, argv = eat_filenames [] argv in
  set_terminal_width ();
  if !doc_builtins then begin
    API.BuiltIn.document_file Builtin.std_builtins;
    exit 0;
  end;
  if !print_deps then begin
    let pl = files |> List.map (fun file -> raising (fun () -> or_exit (API.Parse.program ~flags ~elpi file))) in
    let all = List.map (fun p -> raising (fun () -> or_exit (API.Compile.scope_ast ~flags ~elpi p))) pl |> List.concat in
    let name_of = API.Compile.scoped_program_name in
    let all = List.sort (fun p1 p2 -> compare (name_of p1) (name_of p2)) all in
    let all =
      let rec undup = function
        | [] -> []
        | x :: y :: rest when name_of x = name_of y -> undup (y :: rest)
        | x :: rest -> x :: undup rest in
      undup all in
    Printf.printf "digraph deps {\n";
    all |> List.iter (fun x ->
      let deps = API.Compile.scoped_program_deps x in
      deps |> List.iter (fun d -> Printf.printf "%S -> %S;\n" (name_of x) (fst d)));
    Printf.printf "}\n";
    exit 0
  end;
  let file =
    match files with
    | [] -> "/dev/null"
    | [x] -> x
    | _ -> Printf.eprintf "Only one file can be specified"; exit 1 in
  let t0_parsing = Unix.gettimeofday () in
  let p, parse_errors, parse_warnings = raising (fun () -> API.Parse.program ~flags ~elpi file) in
  let g =
    if !test then
      query_or_exit (API.Parse.query ~elpi ~loc:(API.Ast.Loc.initial "(-test)") ~text:"main.")
    else if !exec <> "" then
      query_or_exit (API.Parse.query ~elpi
        ~loc:(API.Ast.Loc.initial "(-exec)")
        ~text:(Printf.sprintf "%s [%s]." !exec
          String.(concat ", " (List.map (Printf.sprintf "\"%s\"") argv))))
    else begin
     Printf.printf "goal> %!";
     let buff = Lexing.from_channel stdin in
     query_or_exit (API.Parse.query_from ~elpi ~loc:(API.Ast.Loc.initial "(stdin)") buff)
    end in
  if !print_ast then begin
    report_warnings parse_warnings;
    report parse_errors;
    Format.eprintf "%a" API.Pp.Ast.program p;
    Format.eprintf "%a" API.Pp.Ast.query g;
    exit 0;
  end;
  
  Format.eprintf "@\nParsing time: %5.3f@\n%!" (Unix.gettimeofday () -. t0_parsing);
  let query, prog, exec, (type_checking_time, det_checking_time) =
    let t0_compilation = Unix.gettimeofday () in
    try
      let prog, compile_errors, compile_warnings = raising (fun () -> API.Compile.program ~flags ~elpi p) in
      (* the syntax errors, then the errors of the compiler *)
      let prog = or_exit (prog, parse_errors @ compile_errors, parse_warnings @ compile_warnings) in
      let query = query_or_exit (API.Compile.query prog g) in
      let type_checking_time = API.Compile.total_type_checking_time query, API.Compile.total_det_checking_time query in
      let exec = API.Compile.optimize query in
      Format.eprintf "@\nCompilation time: %5.3f@\n%!" (Unix.gettimeofday () -. t0_compilation);
      query, prog, exec, type_checking_time
    with API.Error.ElpiError e -> report [ e ]; exit 1
  in
  Format.eprintf "@\nTypechecking time: %5.3f@\n%!" type_checking_time;
  Format.eprintf "Determinacy checking time: %5.3f@\n%!" det_checking_time;
  if !print_lprolog then begin
    API.Pp.program Format.std_formatter prog;
    Format.printf "\n\n%% query\n?- ";
    API.Pp.goal Format.std_formatter query;
    exit 0;
  end;
  if !print_passes || !print_units then begin
    exit 0;
  end;
  if not !batch then 
    raising (fun () -> API.Execute.loop
      ~delay_outside_fragment:!delay_outside_fragment ~more ~pp:print_solution
      exec)
  else begin
    Gc.compact ();
    if
      let t0 = Unix.gettimeofday () in
      let b = raising (fun () -> API.Execute.once
          ~delay_outside_fragment:!delay_outside_fragment exec) in
      let t1 = Unix.gettimeofday () in
      match b with
      | API.Execute.Success _ -> print_solution (t1 -. t0) b; true
      | (API.Execute.Failure | API.Execute.NoMoreSteps) -> false
    then exit 0
    else exit 1
  end
;;
