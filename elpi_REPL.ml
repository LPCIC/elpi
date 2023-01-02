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
  "\nUsage: elpi [OPTION].. [FILE].. [-- ARGS..] \n" ^ 
  "\nMain options:\n" ^ 
  "\t-main runs the query \"main\"\n" ^ 
  "\t-test runs the query \"main\" (deprecated)\n" ^ 
  "\t-exec pred  runs the query \"pred ARGS\"\n" ^ 
  "\t-D var  Define variable (conditional compilation)\n" ^ 
  "\t-document-builtins Print documentation for built-in predicates\n" ^
  "\t-no-tc don't typecheck the program\n" ^ 
  "\t-I PATH  search for accumulated files in PATH\n" ^
  "\t-delay-problems-outside-pattern-fragment (deprecated, for Teyjus\n" ^
  "\t                                          compatibility)\n" ^
  "\t-legacy-parser enable the legacy parser (deprecated)\n"^
  "\t-legacy-parser-available exists with 0 if it is the case\n"^
  "\t--version prints the version of Elpi (also -v or -version)\n" ^ 
  "\t--help prints this help (also -h or -help)\n" ^ 
 API.Setup.usage ^
  "\nDebug options (for debugging Elpi, not your program):\n" ^ 
  "\t-parse-term parses a term from standard input and prints it\n" ^ 
  "\t-print-ast prints files as parsed, then exit\n" ^ 
  "\t-print prints files after most compilation passes, then exit\n" ^ 
  "\t-print-passes prints intermediate data during compilation, then exit\n" ^
  "\t-print-units prints compilation units data, then exit\n"
;;

(* For testing purposes we declare an identity quotation *)
let _ =
  API.Quotation.register_named_quotation ~name:"elpi"
    API.Quotation.lp

let _ =
  let main = ref false in
  let exec = ref "" in
  let print_lprolog = ref false in
  let print_ast = ref false in
  let typecheck = ref true in
  let batch = ref false in
  let doc_builtins = ref false in
  let delay_outside_fragment = ref false in 
  let print_passes = ref false in
  let print_units = ref false in
  let extra_paths = ref [] in
  let legacy_parser = ref false in
  let parse_term = ref false in
  let vars =
    ref API.Compile.(default_flags.defined_variables) in
  let rec eat_options = function
    | [] -> []
    | "-delay-problems-outside-pattern-fragment" :: rest -> delay_outside_fragment := true; eat_options rest
    | "-legacy-parser" :: rest -> legacy_parser := true; eat_options rest
    | "-legacy-parser-available" :: _ ->
          if API.Setup.legacy_parser_available then exit 0 else exit 1
    | "-main" :: rest -> batch := true; main := true; eat_options rest
    | "-test" :: rest -> batch := true; main := true; eat_options rest
    | "-exec" :: goal :: rest ->  batch := true; exec := goal; eat_options rest
    | "-print" :: rest -> print_lprolog := true; eat_options rest
    | "-print-ast" :: rest -> print_ast := true; eat_options rest
    | "-print-passes" :: rest -> print_passes := true; eat_options rest
    | "-print-units" :: rest -> print_units := true; eat_options rest
    | "-parse-term" :: rest -> parse_term := true; eat_options rest
    | "-no-tc" :: rest -> typecheck := false; eat_options rest
    | "-document-builtins" :: rest -> doc_builtins := true; eat_options rest
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
      API.Compile.print_passes = !print_passes;
      API.Compile.print_units = !print_units;
  } in
  let elpi =
    API.Setup.init
      ~legacy_parser:!legacy_parser
      ~flags:(API.Compile.to_setup_flags flags)
      ~builtins:[Builtin.std_builtins]
      ~file_resolver:(API.Parse.std_resolver ~paths ())
      () in
  if !parse_term then begin
    let g =
      try API.Parse.goal_from ~elpi ~loc:(API.Ast.Loc.initial "(-parse-term)") (Lexing.from_channel stdin)
      with API.Parse.ParseError(loc,msg) -> Format.eprintf "%a@;%s\n" API.Ast.Loc.pp loc msg; exit 1 in
    Format.printf "Raw term: %a\n" API.Pp.Ast.query g;
    let p = API.Parse.program ~elpi ~files:[] in
    let prog = API.Compile.program ~flags ~elpi [p] in
    let query = API.Compile.query prog g in
    Format.printf "Compiled term: %a\n" API.Pp.goal query;
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
    API.BuiltIn.document_file
      ~header:"% File generated by elpi -document-builtins, do not edit"
      Builtin.std_builtins;
    exit 0;
  end;
  let t0_parsing = Unix.gettimeofday () in
  let p =
    try API.Parse.program ~elpi ~files
    with API.Parse.ParseError(loc,err) ->
      Printf.eprintf "%s\n%s\n" (API.Ast.Loc.show loc) err;
      exit 1;
  in
  let g =
    if !main then
      API.Parse.goal ~elpi ~loc:(API.Ast.Loc.initial "(-main)") ~text:"main."
    else if !exec <> "" then
      begin API.Parse.goal ~elpi
        ~loc:(API.Ast.Loc.initial "(-exec)")
        ~text:(Printf.sprintf "%s [%s]." !exec
          String.(concat ", " (List.map (Printf.sprintf "\"%s\"") argv)))
         end
    else begin
     Printf.printf "goal> %!";
     let buff = Lexing.from_channel stdin in
     try API.Parse.goal_from ~elpi ~loc:(API.Ast.Loc.initial "(stdin)") buff
     with API.Parse.ParseError(loc,err) ->
        Printf.eprintf "%s:\n%s\n" (API.Ast.Loc.show loc) err;
        exit 1;
    end in
  if !print_ast then begin
    Format.eprintf "%a" API.Pp.Ast.program p;
    Format.eprintf "%a" API.Pp.Ast.query g;
    exit 0;
  end;
  
  Format.eprintf "@\nParsing time: %5.3f@\n%!" (Unix.gettimeofday () -. t0_parsing);
  let query, exec =
    let t0_compilation = Unix.gettimeofday () in
    try
      let prog = API.Compile.program ~flags ~elpi [p] in
      let query = API.Compile.query prog g in
      let exec = API.Compile.optimize query in
      Format.eprintf "@\nCompilation time: %5.3f@\n%!" (Unix.gettimeofday () -. t0_compilation);
      query, exec
    with API.Compile.CompileError(loc,msg) ->
      API.Utils.error ?loc msg
  in
  if !typecheck then begin
    let t0 = Unix.gettimeofday () in
    let b = API.Compile.static_check ~checker:(Builtin.default_checker ()) query in
    Format.eprintf "@\nTypechecking time: %5.3f@\n%!" (Unix.gettimeofday () -. t0);
    if not b then begin
       Format.eprintf "Type error. To ignore it, pass -no-tc.\n";
       exit 1
    end;
  end;
  if !print_lprolog then begin
    API.Pp.program Format.std_formatter query;
    Format.printf "?- ";
    API.Pp.goal Format.std_formatter query;
    exit 0;
  end;
  if !print_passes || !print_units then begin
    exit 0;
  end;
  if not !batch then 
    API.Execute.loop
      ~delay_outside_fragment:!delay_outside_fragment ~more ~pp:print_solution
      exec
  else begin
    Gc.compact ();
    if
      let t0 = Unix.gettimeofday () in
      let b = API.Execute.once
          ~delay_outside_fragment:!delay_outside_fragment exec in
      let t1 = Unix.gettimeofday () in
      match b with
      | API.Execute.Success _ -> print_solution (t1 -. t0) b; true
      | (API.Execute.Failure | API.Execute.NoMoreSteps) -> false
    then exit 0
    else exit 1
  end
;;
