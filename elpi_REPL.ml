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
    let ic, _ as p = Unix.open_process "tput cols" in
    let w = int_of_string (input_line ic) in
    let _ = Unix.close_process p in w
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
  "\t-test runs the query \"main\"\n" ^ 
  "\t-exec pred  runs the query \"pred ARGS\"\n" ^ 
  "\t-D var  Define variable (conditional compilation)\n" ^ 
  "\t-document-builtins Print documentation for built-in predicates\n" ^
  "\t-no-tc don't typecheck the program\n" ^ 
  "\t-delay-problems-outside-pattern-fragment (deprecated, for Teyjus\n" ^
  "\t                                          compatibility)\n" ^
  "\t-version prints the version of Elpi\n" ^ 
 API.Setup.usage ^
  "\nDebug options (for debugging Elpi, not your program):\n" ^ 
  "\t-print-accumulated-files prints files loaded via accumulate\n" ^ 
  "\t-print-ast prints files as parsed, then exit\n" ^ 
  "\t-print prints files after most compilation passes, then exit\n" ^ 
  "\t-print-passes prints intermediate data during compilation, then exit\n"
;;

(* For testing purposes we declare an identity quotation *)
let _ =
  API.Quotation.register_named_quotation ~name:"elpi"
    API.Quotation.lp

let _ =
  let test = ref false in
  let exec = ref "" in
  let args = ref [] in
  let print_lprolog = ref false in
  let print_ast = ref false in
  let typecheck = ref true in
  let batch = ref false in
  let doc_builtins = ref false in
  let delay_outside_fragment = ref false in 
  let print_passes = ref false in
  let print_accumulated_files = ref false in
  let vars =
    ref API.Compile.(default_flags.defined_variables) in
  let rec aux = function
    | [] -> []
    | "-delay-problems-outside-pattern-fragment" :: rest -> delay_outside_fragment := true; aux rest
    | "-test" :: rest -> batch := true; test := true; aux rest
    | "-exec" :: goal :: rest ->  batch := true; exec := goal; aux rest
    | "-print" :: rest -> print_lprolog := true; aux rest
    | "-print-ast" :: rest -> print_ast := true; aux rest
    | "-print-passes" :: rest -> print_passes := true; aux rest
    | "-print-accumulated-files" :: rest ->
      print_accumulated_files := true; aux rest
    | "-no-tc" :: rest -> typecheck := false; aux rest
    | "-document-builtins" :: rest -> doc_builtins := true; aux rest
    | "-D" :: var :: rest ->
      vars := API.Compile.StrSet.add var !vars;
      aux rest
    | ("-h" | "--help") :: _ -> Printf.eprintf "%s" usage; exit 0
    | "-version" :: _ ->
        Printf.printf "%s\n" "%%VERSION_NUM%%";
        exit 0
    | "--" :: rest -> args := rest; []
    | s :: _ when String.length s > 0 && s.[0] == '-' ->
        Printf.eprintf "Unrecognized option: %s\n%s" s usage; exit 1
    | x :: rest -> x :: aux rest in
  let cwd = Unix.getcwd () in
  let tjpath =
    let v = try Sys.getenv "TJPATH" with Not_found -> "" in
    let tjpath = Str.split (Str.regexp ":") v in
    List.flatten (List.map (fun x -> ["-I";x]) tjpath) in
  let installpath = 
    let v = try Sys.getenv "OCAMLPATH" with Not_found -> "" in
    let ocamlpath =
      (Filename.dirname Sys.executable_name ^ "/../lib/") ::
      (Filename.dirname Sys.executable_name ^ "/../lib/ocaml") ::
      Str.split (Str.regexp ":") v in
    List.flatten (List.map (fun x -> ["-I";x^"/elpi/"]) ocamlpath) in
  let execpath = ["-I"; Filename.dirname (Sys.executable_name)] in
  let opts = Array.to_list Sys.argv @ tjpath @ installpath @ execpath in
  let pheader, argv = API.Setup.init ~builtins:Builtin.std_builtins opts ~basedir:cwd in
  let filenames = aux (List.tl argv) in
  set_terminal_width ();
  if !doc_builtins then begin
    API.BuiltIn.document Format.std_formatter
      Builtin.std_declarations;
    exit 0;
  end;
  let p =
    try API.Parse.program
          ~print_accumulated_files:!print_accumulated_files filenames
    with API.Parse.ParseError(loc,err) ->
      Printf.eprintf "%s: %s\n" (API.Ast.Loc.show loc) err;
      exit 1;
  in
  if !print_ast then begin
    Format.eprintf "%a" API.Pp.Ast.program p;
    exit 0;
  end;
  let g =
    if !test then API.Parse.goal (API.Ast.Loc.initial "(-test)") "main."
    else if !exec <> "" then
      begin API.Parse.goal
        (API.Ast.Loc.initial "(-exec)")
        (Printf.sprintf "%s [%s]." !exec
          String.(concat ", " (List.map (Printf.sprintf "\"%s\"") !args)))
         end
    else begin
     Printf.printf "goal> %!";
     let strm = Stream.of_channel stdin in
     try API.Parse.goal_from_stream (API.Ast.Loc.initial "(stdin)") strm
     with API.Parse.ParseError(loc,err) ->
        Printf.eprintf "%s: %s\n" (API.Ast.Loc.show loc) err;
        exit 1;
    end in
  let flags = {
    API.Compile.default_flags with
      API.Compile.defined_variables = !vars;
      API.Compile.print_passes = !print_passes;
  } in
  let prog = API.Compile.program ~flags pheader [p] in
  let query = API.Compile.query prog g in
  if !typecheck then begin
    let t0 = Unix.gettimeofday () in
    let b = API.Compile.static_check ~flags query in
    Format.eprintf "@\nTypechecking time: %5.3f@\n%!" (Unix.gettimeofday () -. t0);
    if not b then begin
       Format.eprintf "Type error. To ignore it, pass -no-tc.\n";
       exit 1
    end;
  end;
  if !print_lprolog then begin
    API.Pp.query Format.std_formatter query;
    exit 0;
  end;
  let exec = API.Compile.link query in
  if !print_passes then begin
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
