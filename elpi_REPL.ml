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

let print_solution time = function
| Elpi_API.Execute.NoMoreSteps ->
   Format.eprintf "Interrupted (no more steps)@\n%!"
| Elpi_API.Execute.Failure -> Format.eprintf "Failure@\n%!"
| Elpi_API.Execute.Success {
    Elpi_API.Data.assignments; constraints; custom_constraints } ->
  Format.eprintf "@\nSuccess:@\n%!" ;
  Elpi_API.Data.StrMap.iter (fun name v ->
    Format.eprintf "  @[<hov 1>%s = %a@]@\n%!" name
      Elpi_API.Pp.term v) assignments;
  Format.eprintf "@\nTime: %5.3f@\n%!" time;
  Format.eprintf "@\nConstraints:@\n%a@\n%!"
    Elpi_API.Pp.constraints constraints;
  Format.eprintf "@\nCustom constraints:@\n%a@\n%!"
    Elpi_API.Pp.custom_constraints custom_constraints;
;;
  
let more () =
  prerr_endline "\nMore? (Y/n)";
  read_line() <> "n"
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
  "\t-where print system wide installation path then exit\n" ^ 
  "\t-print-latex prints files to LaTeX syntax, then exit\n" ^ 
  "\t-print prints files after desugar, then exit\n" ^ 
  "\t-print-ast prints files as parsed, then exit\n" ^ 
  Elpi_API.Setup.usage
;;

let _ =
  let test = ref false in
  let exec = ref "" in
  let args = ref [] in
  let print_prolog = ref false in
  let print_latex = ref false in
  let print_lprolog = ref false in
  let print_ast = ref false in
  let typecheck = ref true in
  let batch = ref false in
  if List.mem "-where" (Array.to_list Sys.argv) then begin
    Printf.printf "%s\n" Elpi_config.install_dir; exit 0 end;
  let rec aux = function
    | [] -> []
    | "-test" :: rest -> batch := true; test := true; aux rest
    | "-exec" :: goal :: rest ->  batch := true; exec := goal; aux rest
    | "-print-prolog" :: rest -> print_prolog := true; aux rest
    | "-print-latex" :: rest -> print_latex := true; aux rest
    | "-print" :: rest -> print_lprolog := true; aux rest
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
  let installpath = [ "-I"; Elpi_config.install_dir ] in
  let execpath = ["-I"; Filename.dirname (Sys.executable_name)] in
  let opts = Array.to_list Sys.argv @ tjpath @ installpath @ execpath in
  let argv = Elpi_API.Setup.init ~silent:false opts cwd in
  let filenames = aux (List.tl argv) in
  set_terminal_width ();
  if !print_latex then Elpi_API.Temporary.activate_latex_exporter () ;
  let p = Elpi_API.Parse.program filenames in
  if !print_ast then begin
    Format.eprintf "%a" Elpi_API.Pp.Ast.program p;
    exit 0;
  end;
  if !print_latex then exit 0;
  let g =
    if !test then Elpi_API.Parse.goal "main."
    else if !exec <> "" then
      begin Elpi_API.Parse.goal
        (Printf.sprintf "%s [%s]." !exec
          String.(concat ", " (List.map (Printf.sprintf "\"%s\"") !args)))
         end
    else begin
     Printf.printf "goal> %!";
     let strm = Stream.of_channel stdin in
     Elpi_API.Parse.goal_from_stream strm
    end in
  let prog = Elpi_API.Compile.program [p] in
  let query = Elpi_API.Compile.query prog g in
  if !typecheck then begin
    if not (Elpi_API.Compile.static_check query) then
       Format.eprintf "Type error\n";
  end;
  if !print_lprolog then begin
    Elpi_API.Pp.query Format.std_formatter query;
    exit 0;
  end;
  let exec = Elpi_API.Compile.link query in
  if not !batch then 
    Elpi_API.Execute.loop exec ~more ~pp:print_solution
  else begin
    Gc.compact ();
    if
      let t0 = Unix.gettimeofday () in
      let b = Elpi_API.Execute.once exec in
      let t1 = Unix.gettimeofday () in
      match b with
      | Elpi_API.Execute.Success _ -> print_solution (t1 -. t0) b; true
      | (Elpi_API.Execute.Failure | Elpi_API.Execute.NoMoreSteps) -> false
    then exit 0
    else exit 1
  end
;;
