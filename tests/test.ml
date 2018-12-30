(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Test_suite
open Suite
    
module Printer : sig

  type status = [ `OK | `KO | `SKIPPED | `TIMEOUT | `RUNNING ]
  val print :
    executable:string -> name:string -> description:string -> float -> float -> int -> status -> unit

  val print_header :
    executables:string list -> seed:int -> timeout:float -> unit
    
  val print_summary :
    total:int -> ok:int -> ko:int -> skipped:int -> unit

end = struct
open ANSITerminal

type status = [ `OK | `KO | `SKIPPED | `TIMEOUT | `RUNNING ]
let print_state col s = printf [col] "%-9s%!" s
let print_timing name t1 t2 mem ex = printf [] "%-20s %6.2f %6.2f %6.1fM  %s%!" name t1 t2 (float_of_int mem /. 1024.0) ex
let print_info name descr ex = printf [] "%-43s %s" (name ^" ("^descr^")") ex

let print ~executable ~name ~description:descr t1 t2 mem = function
  | `OK -> print_state green "OK"; print_timing name t1 t2 mem executable
  | `TIMEOUT -> print_state red "TIMEOUT"; print_info name descr executable
  | `KO -> print_state red "KO"; print_info name descr executable
  | `RUNNING -> print_state blue "RUNNING"; print_info name descr executable
  | `SKIPPED -> print_state yellow "SKIPPED"; print_info name descr executable

let print_header ~executables ~seed ~timeout =
  printf [blue] "-----------------------------------------------------------\n";
  printf [blue] "Runners:"; printf [] " %s\n" (String.concat " " executables);
  printf [blue] "Random seed:"; printf [] " %d\n" seed;
  printf [blue] "Timeout:"; printf [] " %.2f seconds\n" timeout;
  printf [blue] "\n";
  printf [blue] "status   test                  time   wall   mem     runner\n";
  printf [blue] "-----------------------------------------------------------\n";
;;

let print_summary ~total ~ok ~ko ~skipped =
  printf [blue] "-----------------------------------------------------------\n";
  printf [blue] "Tests: "; printf [] "%d\n" total;
  printf [blue] "Passed: "; printf [] "%d\n" ok;
  printf [blue] "Failed: "; printf [] "%d\n" ko;
  printf [blue] "Skipped: "; printf [] "%d\n" skipped;
;;

end

let run timeout _seed sources env { Runner.run; test; executable }  =

  let { Test.name; description; _ } = test in
  let print = Printer.print ~executable:(Filename.basename executable) ~name ~description in

  print 0.0 0.0 0 `RUNNING;
  ANSITerminal.move_bol ();

  let rc = match run ~timeout ~env ~sources with
    | Runner.Skipped -> print 0.0 0.0 0 `SKIPPED; None
    | Runner.Done ({ Runner.rc; _ } as x) ->
      begin match rc with
        | Runner.Timeout timeout -> print timeout timeout 0 `TIMEOUT
        | Runner.Failure { Runner.time; walltime; mem } ->
            print time walltime mem `KO
        | Runner.Success { Runner.time; walltime; mem } ->
            print time walltime mem `OK
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
      | Some { Runner.rc; executable; test = { Test.name; _ } } ->
          begin match rc with
          | Runner.Timeout _ -> ()
          | Runner.Failure _ -> ()
          | Runner.Success { Runner.time; walltime; mem } ->
              Printf.fprintf oc "%s,%s,%f,%f,%d\n"
                executable name time walltime mem
          end
      | None -> ());
  close_out oc;
  ignore(Sys.command (plot ^ " data.csv"));
  ignore(Sys.command "gnuplot data.csv.plot")
;;


let main sources plot timeout executables namef timetool seed =
  Random.init seed;
  let filter_name =
    let rex = Str.regexp (".*"^namef) in
    fun ~name:x -> Str.string_match rex x 0 in
  let cruft = "CRUFT="^ String.make (Random.bits () mod (2 lsl 16)) 'x' in
  let env = Array.concat [[|cruft|];Unix.environment ()] in
  let tests = Suite.Test.get filter_name in
  Printer.print_header ~executables ~seed ~timeout;
  let jobs =
    tests |> List.map (Suite.Runner.jobs ~timetool ~executables)
          |> List.concat in
  let results =
    List.map (run timeout seed sources env) jobs in
  let total, ok, ko, skipped =
    let skip, rest =
      List.partition (function None -> true | _ -> false) results in
    let ok, ko =
      List.partition (function
        | Some { Runner.rc = Runner.Success _; _ } -> true
        | _ -> false) rest in
    List.(length jobs, length ok, length ko, length skip) in
  Printer.print_summary ~total ~ok ~ko ~skipped;
  if List.length executables > 1 then print_csv plot results;
  if ko = 0 then exit 0 else exit 1

open Cmdliner

let runners =
  let doc = "Run tests against $(docv)." in
  Arg.(non_empty & opt_all non_dir_file [] & info ["runner"] ~docv:"RUNNER" ~doc)

let namef =
  let doc = "Run only tests with a name that matches $(docv)." in
  Arg.(value & opt string "." & info ["name-match"] ~docv:"REX" ~doc)

let seed =
  let doc = "Uses $(docv) as the random number generator seed." in
  Arg.(value & opt int 0 & info ["seed"] ~docv:"INT" ~doc)

let timeout =
  let doc = "Uses $(docv) as the timeout (in seconds)." in
  Arg.(value & opt float 30.0 & info ["timeout"] ~docv:"FLOAT" ~doc)

let src =
  let doc = "Looks for the sources in $(docv)." in
  Arg.(value & opt dir "sources/" & info ["sources"] ~docv:"DIR" ~doc)

let plot =
  let doc = "Path for the plot utility is $(docv)." in
  Arg.(value & opt non_dir_file "./plot" & info ["plot"] ~docv:"PATH" ~doc)

let mem =
  let doc = "Uses $(docv) as the tool to measure memory." in
  Arg.(value & opt non_dir_file "/usr/bin/time" & info ["time"] ~docv:"PATH" ~doc)

let info =
  let doc = "run the test suite" in
  let tests = Test.names ()
    |> List.map (fun (cat,ts) -> [ `I(cat,String.concat ", " ts) ])
    |> List.concat in
  let man = [`Blocks [`S "KNOWN TESTS" ; `Blocks tests ] ] in
  Term.info ~doc ~exits:Term.default_exits ~man "test" 
;;

let () =
  Term.exit @@ Term.eval (Term.(const main $ src $ plot $ timeout $ runners $ namef $ mem $ seed), info)
