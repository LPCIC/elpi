(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Test_suite
open Suite
    
module Printer : sig

  type status = [ `OK | `KO | `SKIPPED | `TIMEOUT | `RUNNING | `PROMOTE ]
  val print :
    executable:string -> name:string -> description:string -> promote:bool -> float -> float -> float -> int -> status -> unit

  val print_header :
    executables:string list -> seed:int -> timeout:float -> unit
    
  val print_summary :
    total:int -> ok:int -> ko_list:string list -> skipped:int -> timeout:int -> unit

  val print_log :
    ln_nb:int -> fname:string -> unit

end = struct
open ANSITerminal

type status = [ `OK | `KO | `SKIPPED | `TIMEOUT | `RUNNING | `PROMOTE ]
let print_state col s = printf [col] "%-9s%!" s
let print_timing name t0 t1 t2 mem ex = printf [] "%-20s %6.2f %6.2f %6.2f %6.1fM  %s%!" name t0 t1 t2 (float_of_int mem /. 1024.0) ex
let print_info name descr ex = printf [] "%-43s %s" (name ^" ("^descr^")") ex

let print ~executable ~name ~description:descr ~promote t0 t1 t2 mem = function
  | `OK -> print_state green "OK"; print_timing name t0 t1 t2 mem executable
  | `PROMOTE -> print_state green "PROMOTE"; print_timing name t0 t1 t2 mem executable
  | `TIMEOUT -> print_state red "TIMEOUT"; print_info name descr executable
  | `KO -> print_state red "KO"; print_info name descr executable
  | `RUNNING -> print_state blue "RUNNING"; print_info name descr executable
  | `SKIPPED -> print_state yellow "SKIPPED"; print_info name descr executable

let print_header ~executables ~seed ~timeout =
  printf [blue] "------------------------------------------------------------------\n";
  printf [blue] "Runners:"; printf [] " %s\n" (String.concat " " executables);
  printf [blue] "Random seed:"; printf [] " %d\n" seed;
  printf [blue] "Timeout:"; printf [] " %.2f seconds\n" timeout;
  printf [blue] "Fiber stack:"; printf [] " %d\n" (Gc.get ()).Gc.stack_limit;
  printf [blue] "\n";
  printf [blue] "status   test                  time   typchk wall   mem     runner\n";
  printf [blue] "------------------------------------------------------------------\n";
;;

let print_summary ~total ~ok ~ko_list ~skipped ~timeout =
  printf [blue] "------------------------------------------------------------------\n";
  let print_stat ?(to_print=false) k v =
    if to_print || v <> 0 then (printf [blue] "%s: " k; printf [] "%d\n" v)
  in
  print_stat ~to_print:true "Tests" total;
  print_stat ~to_print:true "Passed" ok;
  print_stat ~to_print:true "Failed" (List.length ko_list);
  print_stat "Skipped" skipped;
  print_stat "Timeout" timeout;
  if ko_list <> [] then 
    printf [red] "Rerun failed: make tests ONLY=\"'^\\(%s\\)'\"\n" (String.concat "\\|" ko_list)
;;

let print_file ~ln_nb fname =
  let pos = ref 0 in
  let arr = Array.init (max 0 ln_nb) (fun _ -> fun () -> ()) in
  let print_s s () = printf [] "%s\n" s in
  let print_aux =
    if ln_nb = 0 then fun _ -> () else
    if ln_nb > ~-1 then 
      fun s -> (arr.(!pos) <- print_s s; pos := (!pos + 1) mod ln_nb;)
    else fun s -> printf [] "%s\n" s in
  try
    let ic = open_in fname in
    while true do
      let s = input_line ic in
      print_aux s
    done
  with
  | End_of_file -> for i = 0 to ln_nb - 1 do arr.((i + !pos) mod ln_nb) (); done
  | e -> printf [red] "Error reading %s: %s\n" fname (Printexc.to_string e)


let print_log ~ln_nb ~fname =
  printf [red] "------------------------------------------------------------------\n";
  printf [blue] "Log of the first failure: "; printf [] "%s\n" fname;
  printf [red] "------------------------------------------------------------------\n";
  print_file ~ln_nb fname;
  printf [red] "------------------------------------------------------------------\n";
  printf [blue] "End log of the first failure: "; printf [] "%s\n" fname;
  printf [red] "------------------------------------------------------------------\n";

end

let aNSITerminal_move_bol () =
  if Sys.win32 then ANSITerminal.printf [] "\n%!"
  else ANSITerminal.move_bol ()

let run timeout _seed sources promote env { Runner.run; test; executable }  =

  let { Test.name; description; _ } = test in
  let print = Printer.print ~executable:(Filename.basename executable) ~name ~description ~promote in

  print 0.0 0.0 0.0 0 `RUNNING;
  aNSITerminal_move_bol ();

  let rc = match run ~timeout ~env ~sources with
    | Runner.Skipped -> print 0.0 0.0 0.0 0 `SKIPPED; None
    | Runner.Done ({ Runner.rc; _ } as x) ->
      begin match rc with
        | Runner.Timeout timeout -> print timeout timeout timeout 0 `TIMEOUT
        | Runner.Failure { Runner.execution; typechecking; walltime; mem } ->
            print execution typechecking walltime mem `KO
        | Runner.Success { Runner.execution; typechecking; walltime; mem } ->
            print execution typechecking walltime mem `OK
        | Runner.Promote { Runner.execution; typechecking; walltime; mem } ->
            print execution typechecking walltime mem `PROMOTE
      end;
      Some x
  in
  ANSITerminal.(erase Eol);
  ANSITerminal.printf [] "\n%!";
  rc

let print_csv plot results =
  let oc = open_out "data.csv" in
  results |> List.iter
    (function 
      | Some { Runner.rc; executable; test = { Test.name; _ }; _ } ->
          begin match rc with
          | Runner.Timeout _ -> ()
          | Runner.Failure _ -> ()
          | Runner.Success { Runner.execution; walltime; mem; _ } -> (* TODO: print typechecking time *)
              Printf.fprintf oc "%s,%s,%f,%f,%d\n"
                executable name execution walltime mem
          | Runner.Promote { Runner.execution; walltime; mem; _ } -> (* TODO: print typechecking time *)
              Printf.fprintf oc "%s,%s,%f,%f,%d\n"
                executable name execution walltime mem
          end
      | None -> ());
  close_out oc;
  if Sys.command "which lua5.1" = 0 && Sys.command "which gnuplot" = 0 then begin
    ignore(Sys.command (plot ^ " data.csv"));
    ignore(Sys.command "gnuplot data.csv.plot")
  end
;;

let rec find_map f = function
  | [] -> raise Not_found
  | x :: xs ->
      match f x with
      | Some y -> y
      | None -> find_map f xs

let main ln_nb sources plot timeout promote executables namef catskip timetool seed =
  Random.init seed;
  let filter_name =
    let rex = Str.regexp (".*"^namef) in
    fun ~name:x -> Str.string_match rex x 0 in
  let cruft = "CRUFT="^ String.make (Random.bits () mod (2 lsl 16)) 'x' in
  let env = Array.concat [[|cruft|];Unix.environment ()] in
  let tests = Suite.Test.get ~catskip filter_name in
  Printer.print_header ~executables ~seed ~timeout;
  let jobs =
    tests |> List.map (Suite.Runner.jobs ~timetool ~executables ~promote)
          |> List.concat in
  let results =
    List.map (run timeout seed sources promote env) jobs in
  let total, ok, ko_list, skipped, timeout =
    let rec part total ok ko_list skipped timeout = function
      | [] -> (total, ok, List.rev ko_list, skipped, timeout)
      | Some {Runner.rc = Success _; _} :: l -> part (total+1) (ok+1) ko_list skipped timeout l
      | Some {rc = Promote _; _} :: l ->        part (total+1) (ok+1) ko_list skipped timeout l
      | Some {rc = Failure _; test} :: l ->        part (total+1) ok (test.name :: ko_list) skipped timeout l
      | None :: l ->                            part (total+1) ok ko_list (skipped+1) timeout l
      | Some {rc = Timeout _; _} :: l ->        part (total+1) ok ko_list skipped (timeout+1) l
    in part 0 0 [] 0 0 results in
  Printer.print_summary ~total ~ok ~ko_list ~skipped ~timeout;
  begin try
    let log_first_failure =
      results |> find_map (function
        | Some { Runner.rc = Runner.Failure _; log; _ } -> Some log
        | _ -> None) in
    Printer.print_log ~ln_nb:ln_nb ~fname:log_first_failure
  with Not_found -> ()
  end;
  if List.length executables > 1 then print_csv plot results;
  if ko_list = [] then exit 0 else exit 1

open Cmdliner

let runners =
  let doc = "Run tests against $(docv)." in
  Arg.(non_empty & opt_all non_dir_file [] & info ["runner"] ~docv:"RUNNER" ~doc)

let valid_category_parser c =
  if List.exists (fun (c',_) -> c = c') (Test.names ())
  then `Ok c
  else `Error ("unknown category " ^ c)

let valid_category = Arg.(valid_category_parser,conv_printer string)

let namef =
  let doc = "Run only tests with a name that matches $(docv)." in
  Arg.(value & opt string "." & info ["name-match"] ~docv:"REX" ~doc)

let catskip =
  let doc = "Skip tests belonging to category $(docv)." in
  Arg.(value & opt_all valid_category [] & info ["cat-skip"] ~docv:"STRING" ~doc)
  
let seed =
  let doc = "Uses $(docv) as the random number generator seed." in
  Arg.(value & opt int 0 & info ["seed"] ~docv:"INT" ~doc)

let timeout =
  let doc = "Uses $(docv) as the timeout (in seconds)." in
  Arg.(value & opt float 30.0 & info ["timeout"] ~docv:"FLOAT" ~doc)

let src =
  let doc = "Looks for the sources in $(docv)." in
  Arg.(value & opt string "sources/" & info ["sources"] ~docv:"DIR" ~doc)

let plot =
  let doc = "Path for the plot utility is $(docv)." in
  Arg.(value & opt non_dir_file "./plot" & info ["plot"] ~docv:"PATH" ~doc)

let mem =
  let doc = "Uses $(docv) as the tool to measure memory." in
  Arg.(value & opt non_dir_file "/usr/bin/time" & info ["time"] ~docv:"PATH" ~doc)

let promote = 
  let doc = "Promotes the tests (if failing)" in
  Arg.(value & opt bool false & info ["promote"] ~docv:"PATH" ~doc)

let ln_nb =
  let doc = "Sets the maximum number of lines to print for failing test (-1 means no max)" in
  Arg.(value & opt int ~-1 & info ["ln_nb"] ~docv:"INT" ~doc)

let info =
  let doc = "run the test suite" in
  let tests = Test.names ()
    |> List.map (fun (cat,ts) -> [ `I(cat,String.concat ", " ts) ])
    |> List.concat in
  let man = [`Blocks [`S "KNOWN TESTS" ; `Blocks tests ] ] in
  (Term.info ~doc ~exits:Term.default_exits ~man "test") [@ warning "-A"]
  (* ocaml >= 4.08 | Cmd.info ~doc ~exits:Cmd.Exit.defaults ~man "test" *)
;;

let () =
  (Term.exit @@ Term.eval (Term.(const main $ ln_nb $ src $ plot $ timeout $ promote $ runners $ namef $ catskip $ mem $ seed),info)) [@ warning "-A"]
  (* ocaml >= 4.08 | exit @@ Cmd.eval (Cmd.v info Term.(const main $ src $ plot $ timeout $ runners $ namef $ catskip $ mem $ seed)) *)
