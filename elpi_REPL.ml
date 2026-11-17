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
  "\t-config FILE  the elpi.toml of the project (default: the nearest one above the file)\n" ^
  "\t-no-config  no elpi.toml\n" ^
  "\t-check-package PKG  checks the installed findlib package PKG: its\n" ^
  "\t         elpi.toml, its plugin and stub, and that each of its .elpi files\n" ^
  "\t         (listed as +PKG/file) compiles where it is installed\n" ^
  "\t-w SPEC  the level of a kind of warnings, after the ones of elpi.toml:\n" ^
  "\t         +name turns name on, -name off, @name makes it an error; all is\n" ^
  "\t         all of them; repeat it for several kinds, the last one wins,\n" ^
  "\t         e.g. -w -linear-variable -w @undeclared-global. The names:\n" ^
  String.concat "" (List.map (fun id -> "\t           " ^ API.Error.warning_name id ^ "\n") API.Error.all_warnings) ^
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
(* the levels of the kinds of warnings (elpi.toml, then -w), and whether a
   warning that is an error was reported *)
let warning_levels = ref []
let warning_errors = ref false

let report_warnings warnings =
  List.iter (fun { API.Error.warning_id; warning = e } ->
    match API.Error.warning_level !warning_levels warning_id with
    | API.Error.Off -> ()
    | API.Error.On -> Format.eprintf "@[<hv>Warning: %a@]\n%!" API.Error.pp e
    | API.Error.As_error -> warning_errors := true; Format.eprintf "@[<hv>Error: %a@]\n%!" API.Error.pp e)
    warnings

(* the compiled query, or its error; the warnings are printed *)
let query_or_exit (q, warnings) =
  report_warnings warnings;
  if !warning_errors then exit 1;
  match q with
  | Ok q -> q
  | Error e -> report [ e ]; exit 1

(* the result of a pass, or the errors it found; the warnings are printed *)
let or_exit (x, errors, warnings) =
  report_warnings warnings;
  report errors;
  if errors <> [] || !warning_errors then exit 1;
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

(* the options of the command line *)
type options = {
  test : bool;
  exec : string;
  print_lprolog : bool;
  print_ast : bool;
  batch : bool;
  doc_builtins : bool;
  doc_infix : bool;
  delay_outside_fragment : bool;
  print_passes : bool;
  print_units : bool;
  extra_paths : string list;
  parse_term : bool;
  parse_clause : bool;
  skip_det_check : bool;
  max_errors : int;
  print_deps : bool;
  config_file : string option;
  no_config : bool;
  check_package : string option;
  warning_specs : string list; (* in order *)
  vars : API.Compile.StrSet.t;
}

(* the options, and the rest of the command line (the files, then -- and the
   arguments of the query, and the options of the trace); -h and -v exit *)
let parse_options argv =
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
  let config_file = ref None and no_config = ref false in
  let check_package = ref None in
  let warning_specs = ref [] in
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
    | "-config" :: f :: rest -> config_file := Some f; eat_options rest
    | "-no-config" :: rest -> no_config := true; eat_options rest
    | "-check-package" :: pkg :: rest -> check_package := Some pkg; eat_options rest
    | "-w" :: spec :: rest -> warning_specs := spec :: !warning_specs; eat_options rest
    | ("-h" | "--help" | "-help") :: _ -> Printf.eprintf "%s" usage; exit 0
    | ("-v" | "--version" | "-version") :: _ -> Printf.printf "%s\n" "%%VERSION_NUM%%"; exit 0
    | "--" :: rest -> "--" :: rest
    | x :: rest -> x :: eat_options rest
  in
  let rest = eat_options argv in
  { test = !test; exec = !exec; print_lprolog = !print_lprolog; print_ast = !print_ast;
    batch = !batch; doc_builtins = !doc_builtins; doc_infix = !doc_infix;
    delay_outside_fragment = !delay_outside_fragment; print_passes = !print_passes;
    print_units = !print_units; extra_paths = !extra_paths; parse_term = !parse_term;
    parse_clause = !parse_clause; skip_det_check = !skip_det_check; max_errors = !max_errors;
    print_deps = !print_deps; config_file = !config_file; no_config = !no_config;
    check_package = !check_package; warning_specs = List.rev !warning_specs; vars = !vars },
  rest

(* elpi -check-package PKG: the package as installed, one line per item; no
   elpi.toml of a project is read *)
let check_package pkg =
  let report = Elpi_dynload.check_package ~pkg in
  let width = List.fold_left (fun w (item, _) -> max w (String.length item)) 0 report |> min 40 in
  let indent = String.make (width + 2) ' ' in
  let indented s = String.concat ("\n" ^ indent) (String.split_on_char '\n' s) in
  let failed = ref false in
  report |> List.iter (fun (item, result) ->
    let pad = String.make (max 1 (width + 2 - String.length item)) ' ' in
    match result with
    | Elpi_dynload.Checked what -> Printf.printf "%s%s%s\n" item pad what
    | Elpi_dynload.Failed errors ->
        failed := true;
        Printf.printf "%s%s%s\n" item pad (String.concat ("\n" ^ indent) (List.map indented errors)));
  exit (if !failed then 1 else 0)

(* the elpi.toml of the project: given, or the nearest one above the file (the
   first argument that is a file, with or without .elpi); it names the
   project being run, found in its sources *)
let project_config options argv =
  let config =
    if options.no_config then None
    else match options.config_file with
      | Some file -> Some (raising (fun () -> Elpi_dynload.config_of_file ~file ()))
      | None ->
          let is_file s = Sys.file_exists s || Sys.file_exists (s ^ ".elpi") in
          match List.find_opt (fun s -> String.length s > 0 && s.[0] <> '-' && is_file s) argv with
          | Some file -> raising (fun () -> Elpi_dynload.config_above ~file ())
          | None -> None in
  Option.iter Elpi_dynload.declare_project config;
  config

(* the warnings: of elpi.toml, then of -w, in order; the ones at run time
   too *)
let set_warnings options config =
  warning_levels :=
    (match config with Some c -> c.Elpi_dynload.warnings | None -> [])
    @ List.concat_map (fun s -> raising (fun () -> API.Error.warning_spec s)) options.warning_specs;
  Builtin.set_runtime_warn (fun ?loc ~id message ->
    let show = match loc with None -> "" | Some loc -> API.Ast.Loc.show loc in
    match API.Error.warning_level !warning_levels id with
    | API.Error.Off -> ()
    | API.Error.On -> Format.eprintf "@[<hv>Warning: %s@,%s@]\n%!" show message
    | API.Error.As_error -> Format.eprintf "@[<hv>Error: %s@,%s@]\n%!" show message; exit 1)

(* where accumulated files are searched: TJPATH, the installation, the
   directory of the command, -I, the directories of [paths] in elpi.toml;
   and the prefixes of [paths] *)
let search_paths options config =
  let tjpath =
    let v = try Sys.getenv "TJPATH" with Not_found -> "" in
    Str.split (Str.regexp ":") v in
  let installpath =
    let v = try Sys.getenv "OCAMLPATH" with Not_found -> "" in
    (Filename.dirname Sys.executable_name ^ "/../lib/") ::
    (Filename.dirname Sys.executable_name ^ "/../lib/ocaml") ::
    Str.split (Str.regexp ":") v in
  let execpath = Filename.dirname (Sys.executable_name) in
  (* the [paths] of elpi.toml: a prefix for the files under it *)
  let config_paths = match config with
    | Some c -> c.Elpi_dynload.paths @ c.Elpi_dynload.dev_only_paths (* the project is its own *)
    | None -> [] in
  tjpath @ installpath @ [execpath] @ options.extra_paths, config_paths

(* the preload and the prelude of elpi.toml *)
let load_project config =
  (* plugins that declare state components or quotations are loaded before
     Setup.init *)
  Option.iter (fun c -> c.Elpi_dynload.preload |> List.iter (fun pkg ->
    raising (fun () -> Elpi_dynload.preload ~pkg))) config;
  (* the prelude: builtins of Setup.init, so that its macros are seen by the
     files *)
  match config with
  | Some c -> raising (fun () -> Elpi_dynload.prelude_builtins c)
  | None -> []

let compile_flags options = {
    API.Compile.defined_variables = options.vars;
    API.Compile.print_units = options.print_units;
    API.Compile.time_typechecking = true;
    API.Compile.skip_det_checking = options.skip_det_check;
    API.Compile.max_errors = options.max_errors;
    API.Compile.builtin_stubs = false;
}

let setup ~flags ~prelude ~paths ~prefixes =
  raising (fun () ->
    API.Setup.init
      ~quotations
      ~flags:(API.Compile.to_setup_flags flags)
      ~builtins:(Builtin.std_builtins :: prelude)
      ~file_resolver:(API.Parse.std_resolver ~prefixes ~paths ())
      ~packages:Elpi_dynload.packages
      ())

(* -document-infix-syntax *)
let document_infix_syntax () =
  Printf.eprintf "%s" Elpi_parser.Parser_config.legacy_parser_compat_error;
  exit 0

(* -parse-term: a term read from stdin, parsed then compiled *)
let parse_term ~flags elpi =
  let g = query_or_exit (API.Parse.query_from ~elpi ~loc:(API.Ast.Loc.initial "(-parse-term)") (Lexing.from_channel stdin)) in
  Format.printf "Raw term: %a\n" API.Pp.Ast.query g;
  let p = raising (fun () -> or_exit (API.Parse.program_from ~flags ~elpi ~loc:(API.Ast.Loc.initial "(parse_term)") ~digest:(Digest.string "")  (Lexing.from_string ""))) in
  let prog = raising (fun () -> or_exit (API.Compile.program ~flags ~elpi p)) in
  let query = query_or_exit (API.Compile.query prog g) in
  Format.printf "Compiled term: %a\n" API.Pp.goal query;
  exit 0

(* -parse-clause: a rule read from stdin, parsed *)
let parse_clause ~flags elpi =
  let p = raising (fun () -> or_exit (API.Parse.program_from ~flags ~elpi ~loc:(API.Ast.Loc.initial "(-parse-clause)") ~digest:(Digest.string "") (Lexing.from_string (read_all stdin)))) in
  Format.printf "Raw clause: %a\n" API.Pp.Ast.program p;
  exit 0

(* the files, then the arguments after -- *)
let files_and_args argv =
  let rec eat_filenames acc = function
    | [] -> List.rev acc, []
    | "--" :: rest -> List.rev acc, rest
    | s :: _ when String.length s > 0 && s.[0] == '-' ->
        Printf.eprintf "Unrecognized option: %s\n%s" s usage; exit 1
    | x :: rest -> eat_filenames (x::acc) rest in
  eat_filenames [] argv

(* -document-builtins *)
let document_builtins () =
  API.BuiltIn.document_file Builtin.std_builtins;
  exit 0

(* -deps: the graph of the accumulated files, for dot *)
let print_deps ~flags elpi files =
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

(* the program in [files] (one at most), its query (main, -exec, or read from
   stdin), compiled and run: in batch mode the exit code says whether it
   succeeded *)
let run options ~flags elpi files argv =
  let file =
    match files with
    | [] -> "/dev/null"
    | [x] -> x
    | _ -> Printf.eprintf "Only one file can be specified"; exit 1 in
  let t0_parsing = Unix.gettimeofday () in
  let p, parse_errors, parse_warnings = raising (fun () ->
    API.Parse.program ~flags ~elpi file) in
  let g =
    if options.test then
      query_or_exit (API.Parse.query ~elpi ~loc:(API.Ast.Loc.initial "(-test)") ~text:"main.")
    else if options.exec <> "" then
      query_or_exit (API.Parse.query ~elpi
        ~loc:(API.Ast.Loc.initial "(-exec)")
        ~text:(Printf.sprintf "%s [%s]." options.exec
          String.(concat ", " (List.map (Printf.sprintf "\"%s\"") argv))))
    else begin
     Printf.printf "goal> %!";
     let buff = Lexing.from_channel stdin in
     query_or_exit (API.Parse.query_from ~elpi ~loc:(API.Ast.Loc.initial "(stdin)") buff)
    end in
  if options.print_ast then begin
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
  if options.print_lprolog then begin
    API.Pp.program Format.std_formatter prog;
    Format.printf "\n\n%% query\n?- ";
    API.Pp.goal Format.std_formatter query;
    exit 0;
  end;
  if options.print_passes || options.print_units then begin
    exit 0;
  end;
  if not options.batch then
    raising (fun () -> API.Execute.loop
      ~delay_outside_fragment:options.delay_outside_fragment ~more ~pp:print_solution
      exec)
  else begin
    Gc.compact ();
    if
      let t0 = Unix.gettimeofday () in
      let b = raising (fun () -> API.Execute.once
          ~delay_outside_fragment:options.delay_outside_fragment exec) in
      let t1 = Unix.gettimeofday () in
      match b with
      | API.Execute.Success _ -> print_solution (t1 -. t0) b; true
      | (API.Execute.Failure | API.Execute.NoMoreSteps) -> false
    then exit 0
    else exit 1
  end

let main () =
  (* Memtrace.trace_if_requested (); <-- new line *)
  (* Hashtbl.randomize (); *)
  let options, argv = parse_options (List.tl (Array.to_list Sys.argv)) in
  Option.iter check_package options.check_package;
  let config = project_config options argv in
  set_warnings options config;
  let paths, prefixes = search_paths options config in
  let prelude = load_project config in
  let flags = compile_flags options in
  if options.doc_infix then document_infix_syntax ();
  let elpi = setup ~flags ~prelude ~paths ~prefixes in
  if options.parse_term then parse_term ~flags elpi;
  if options.parse_clause then parse_clause ~flags elpi;
  let argv = API.Setup.trace argv in
  let files, argv = files_and_args argv in
  set_terminal_width ();
  if options.doc_builtins then document_builtins ();
  if options.print_deps then print_deps ~flags elpi files;
  run options ~flags elpi files argv

let () = main ()
