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

let print_solution time = function
| Elpi_API.Execute.NoMoreSteps ->
   Format.eprintf "Interrupted (no more steps)\n%!"
| Elpi_API.Execute.Failure -> Format.eprintf "Failure\n%!"
| Elpi_API.Execute.Success (s,cs) ->
  Format.eprintf "\nSuccess:\n%!" ;
  List.iter (fun (name, t) ->
    Format.eprintf "  @[<hov 1>%s = %a@]\n%!" name
      Elpi_API.Pp.term t) s;
  Format.eprintf "\nTime: %5.3f\n%!" time;
  Format.eprintf "\nConstraints:\n%a\n%!"
    Elpi_API.Pp.constraints cs.Elpi_API.Data.constraints;
  Format.eprintf "\nCustom constraints:\n%a\n%!"
    Elpi_API.Pp.custom_constraints cs.Elpi_API.Data.custom_constraints;
;;
  
let more () =
  prerr_endline "\nMore? (Y/n)";
  read_line() <> "n"
;;

let run_prog typecheck prog query =
 let prog = Elpi_API.Compile.program prog in
 let query = Elpi_API.Compile.query prog query in
 if typecheck then Elpi_API.Compile.static_check prog query;
 Elpi_API.Execute.loop prog query ~more ~pp:print_solution
;;

let test_impl typecheck prog query =
 let prog = Elpi_API.Compile.program prog in
 let query = Elpi_API.Compile.query prog query in
 if typecheck then Elpi_API.Compile.static_check prog query;
 Gc.compact ();
 let time f p q =
   let t0 = Unix.gettimeofday () in
   let b = f p q in
   let t1 = Unix.gettimeofday () in
   match b with
   | Elpi_API.Execute.Success _ -> print_solution (t1 -. t0) b; true
   | _ -> false in
 if time Elpi_API.Execute.once prog query then exit 0 else exit 1
;;


(* rewrites a lambda-prolog program to first-order prolog *)
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
  "\t-print prints files after desugar, then exit\n" ^ 
  "\t-print-raw prints files after desugar in ppx format, then exit\n" ^ 
  "\t-print-ast prints files as parsed, then exit\n" ^ 
  "\t-I path searches files in path\n" ^ 
  Elpi_API.Setup.usage
;;

let _ =
  let test = ref false in
  let exec = ref "" in
  let args = ref [] in
  let print_lprolog = ref None in
  let print_ast = ref false in
  let typecheck = ref true in
  let batch = ref false in
  let rec aux = function
    | [] -> []
    | "-test" :: rest -> batch := true; test := true; aux rest
    | "-exec" :: goal :: rest ->  batch := true; exec := goal; aux rest
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
  let argv = Elpi_API.Setup.init ~silent:false opts cwd in
  let filenames = aux (List.tl argv) in
  set_terminal_width ();
  let p = Elpi_API.Parse.program filenames in
  if !print_ast then begin
    Format.eprintf "%a" Elpi_API.Pp.Ast.program p;
    exit 0;
  end;
  if !print_lprolog != None then begin
    Format.eprintf "@[<v>";
    let _ = Elpi_API.Compile.program ?print:!print_lprolog [p] in
    Format.eprintf "@]%!";
    exit 0;
    end;
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
  if !batch then test_impl !typecheck [p] g
  else run_prog !typecheck [p] g
;;
