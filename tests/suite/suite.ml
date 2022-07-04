(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
module Test = struct

type fname = string

type expectation =
  | Success
  | Failure
  | SuccessOutput of Str.regexp
  | FailureOutput of Str.regexp
  | SuccessOutputFile of { sample : string; adjust : string -> string; reference : string }

type trace = Off | On of string list

type t = {
  name : string;
  description : string;
  category: string;
  source_elpi : fname option;
  source_teyjus : fname option;
  deps_teyjus : fname list;
  source_dune : fname option;
  source_json : fname option;
  after: string list;
  typecheck : bool;
  input: fname option;
  expectation : expectation;
  outside_llam : bool;
  trace : string list;
  legacy_parser : bool;
}

let tests = ref []

let declare
    name ~description ?source_elpi ?source_teyjus ?(deps_teyjus=[]) ?source_dune ?source_json
    ?after
    ?(typecheck=true) ?input ?(expectation=Success)
    ?(outside_llam=false)
    ?(trace=Off)
    ?(legacy_parser=false)
    ~category
    ()
=
  if List.exists (fun { name = x; _ } -> x = name) !tests then
    failwith ("a test named " ^ name ^ " already exists");
  begin match source_elpi, source_teyjus, source_dune, source_json with
    | None, None, None, None-> failwith ("test "^name^" has no sources");
    | _ -> ()
  end;
  tests := { 
    name;
    description;
    source_elpi;
    source_teyjus;
    deps_teyjus;
    source_dune;
    source_json;
    after = (match after with None -> [] | Some x -> [x]);
    typecheck;
    input;
    expectation;
    category;
    outside_llam;
    legacy_parser;
    trace = (match trace with Off -> [] | On l -> "-trace-on" :: l)
  } :: !tests

module SM = Map.Make(String)
module SS = Set.Make(String)

let get ~catskip filter =
  let filtercat x = List.exists ((=) x) catskip in
  let alltests = List.fold_left (fun acc ({ name; _ } as t) -> SM.add name t acc ) SM.empty !tests in
  let tests = List.filter (fun { name; category; _ } -> not (filtercat category) && filter ~name) !tests in
  let testset = List.fold_left (fun acc { name; _ } -> SS.add name acc ) SS.empty tests in
  let deps = List.fold_left (fun acc { after; _ } -> List.fold_right SS.add after acc ) SS.empty tests in
  let to_add = SS.fold (fun n acc -> if SS.mem n testset then acc else SS.add n acc) deps SS.empty in
  let tests = (SS.elements to_add |> List.map (fun x -> SM.find x alltests)) @ tests in
  List.sort (fun { name = n1; after = a1; _}  { name = n2; after = a2; _} ->
    if List.mem n1 a2 then -1
    else if List.mem n2 a1 then 1
    else String.compare n1 n2
    ) tests


let names () =
  let m = ref SM.empty in
  !tests |> List.iter (fun { name; category; _ } ->
      try m := SM.add category (name :: SM.find category !m) !m
      with Not_found -> m := SM.add category [name] !m);
  SM.bindings !m

end

module Runner = struct

type time = {
  execution : float;
  typechecking : float;
  walltime : float;
  mem : int;
}
type rc = Timeout of float | Success of time | Failure of time

type result = {
  executable : string;
  rc : rc;
  test: Test.t;
  log: string;
}

type 'a output =
  | Skipped
  | Done of 'a

type run =
  executable:string -> timetool:string -> timeout:float -> env:string array -> sources:string ->
    Test.t -> result output

(* Some tests are only for teyjus/elpi *)
type applicability =
  | Not_for_me
  | Can_run_it

type applicable = executable:string -> Test.t -> applicability

let runners : (applicable * run) list ref = ref []

let declare ~applicable ~run =
  runners := (applicable,run) :: !runners 

type job = {
  executable : string;
  test : Test.t;
  run : timeout:float -> env:string array -> sources:string -> result output;
}

let (||>) l f = List.(concat (map f l))

let jobs ~timetool ~executables test =
  executables ||> (fun executable ->
  !runners ||> (fun (applicable,run) ->
     match applicable ~executable test with
     | Not_for_me -> []
     | Can_run_it -> [{ 
         test;
         executable;
         run = (run ~timetool ~executable test)
       }]))

end

module Util = struct

let logdir = "_log"

let open_file_w name =
  Unix.openfile name [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o660

let open_log ~executable { Test.name; _ } =
  begin try Unix.mkdir logdir 0o770 with Unix.Unix_error _ -> () end;
  let name = logdir^"/"^Filename.basename executable^"+"^name^".log" in
  open_file_w name, name

let close_log (fd,_) = Unix.close fd

let open_dummy_log () =
  let name = Filename.temp_file "elpi" "txt" in
  open_file_w name, name

let write (fd,f) s =
  ignore(Unix.write_substring fd s 0 (String.length s))

let open_input name = Unix.openfile name [Unix.O_RDONLY] 0

type rc = Exit of int * float * int | Timeout

let read_timetool_log def fname =
  let rc = ref (def, 0.0, 0) in
  try
    let ic = open_in fname in
    while true do
      try
        let l = input_line ic in
        close_in ic;
        let exit, m,s,c,mem =
          Scanf.sscanf l "%d %d:%d.%d %dk" (fun a b c d e -> a,b,c,d,e) in
        rc := 
          exit,
          float_of_int m *. 60.0 +. float_of_int s +. float_of_int c *. 0.01,
          mem
      with Scanf.Scan_failure _ -> ()
    done;
    !rc
  with End_of_file | Sys_error _ -> !rc


let wait pid timeout timelog =
  let time0 = Unix.gettimeofday () in
  let stop = ref false in
  let rc = ref (Exit(0,0.0,0)) in
  while not !stop do
      let p, status = Unix.waitpid [Unix.WNOHANG] pid in
      if p = pid then begin
        stop := true;
        rc := match status with
          | Unix.WEXITED def ->
              let exit, elapsed, memory = read_timetool_log def timelog in
              Exit(exit, elapsed, memory)
          | _ ->
              let walltime = Unix.gettimeofday () -. time0 in
              Exit (-1,walltime,0)
      end else if Unix.gettimeofday () > time0 +. timeout then begin
        stop := true;
        rc := Timeout;
        Unix.kill (- pid) 9;
      end else Unix.sleepf 0.01
    done;
    !rc


let fork_wait_win ~close_output exe argv env input output error timefile timeout =
  ignore close_output;
  let pid =
    Unix.create_process_env
      exe (Array.of_list argv) env input output error in
  wait pid timeout timefile

let fork_wait_unix ~close_output exe argv env input output error timefile timeout =
  let pid = Unix.fork () in
  if pid = 0 then begin
    let _ = Unix.setsid () in
    let runner =
      Unix.create_process_env
        exe (Array.of_list argv) env input output error in
    let _, rc = Unix.waitpid [] runner in
    match rc with
    | Unix.WEXITED n -> exit n
    | Unix.WSIGNALED _ -> exit 1
    | Unix.WSTOPPED _ -> exit 1
  end else
  try
    Unix.close input;
    if close_output then Unix.close output;
    wait pid timeout timefile
  with Sys.Break -> Unix.kill (- pid) 9; exit 1

let null = if Sys.win32 then "NUL:" else "/dev/null"

let exec ~timeout ?timetool ~env ~log:(output,oname) ?(input=null) ?(error=output,oname) ~executable ~args ?(close_output=true) () =
  Sys.catch_break true;
  let exe, argv, timefile =
    match timetool with
    | None -> executable, executable :: args, null
    | Some timetool -> 
      let timefile = oname ^ ".time" in
      timetool, (timetool :: "-o" :: timefile :: "--format=%x %E %Mk" :: "--" ::
                   executable :: args), timefile in
  Unix.handle_unix_error (fun () ->
    let input = open_input input in
    if Sys.win32 then fork_wait_win ~close_output exe argv env input output (fst error) timefile timeout
    else fork_wait_unix  ~close_output exe argv env input output (fst error) timefile timeout)
    ()

let with_log (_,log) f =
  let cin = open_in log in
  try
    let x = f (fun () -> input_line cin) in
    close_in cin;
    x
  with e -> close_in cin; raise e

let option_map f = function None -> None | Some x -> Some (f x)

let strip_cwd file =
  let name = Filename.temp_file "elpi" "txt" in
  let oc = open_out name in
  let ic = open_in file in
  let rex = Str.regexp_string (Str.global_replace (Str.regexp_string "\\") "/" (Sys.getcwd () ^ Filename.dir_sep)) in
  try
    while true do
      let l = input_line ic in
      let l = Str.global_replace rex "" l in
      output_string oc (l ^ "\n")
    done;
    name
  with End_of_file ->
    close_in ic;
    close_out oc;
    name
    
end

let match_file ~log file adjust reference =
  let file = adjust file in
  Util.write log (Printf.sprintf "Diffing %s against %s\n" file reference);
  match
    Util.exec ~timeout:5.0 ~env:(Unix.environment ())
      ~log ~close_output:false
      ~executable:"diff" ~args:["-u";"--strip-trailing-cr";reference;file] ()
  with
  | Util.Exit(0,_,_) -> true
  | Util.Exit(n,_,_) ->
    Util.write log (Printf.sprintf "Exit code: %d\n" n);
    Util.write log (Printf.sprintf "Promotion: cp %s %s\n" file reference);
    false
  | _ -> false


module Elpi = struct

let is_elpi =
  let rex1 = Str.regexp "elpi.*$" in
  let rex2 = Str.regexp "elpi-trace-elaborator.*$" in
  fun s ->
    let s = Filename.basename s in
    Str.string_match rex1 s 0 && not (Str.string_match rex2 s 0)

let read_time input_line =
  let time = ref 0.0 in
  try while true do
    let l = input_line () in
    if Str.(string_match (regexp "^Time:") l 0) then
      try time := float_of_string (String.sub l 5 (String.length l - 5))
      with _ -> ()
  done; !time
  with End_of_file -> !time

let match_rex rex input_line =
  let b = Buffer.create 100 in
  begin try
    while true do
    let l = input_line () in
    Buffer.add_string b l;
    Buffer.add_string b "\n";
    done
  with End_of_file -> () end;
  let s = Buffer.contents b in
  let s = Str.global_replace (Str.regexp_string "\r") "" s in
  try ignore(Str.search_forward rex s 0); true
  with Not_found -> false

let read_tctime input_line =
  let time = ref 0.0 in
  try while true do
    let l = input_line () in
    if Str.(string_match (regexp "^Typechecking time:") l 0) then
      try time := float_of_string (String.sub l 18 (String.length l - 18))
      with _ -> ()
  done; !time
  with End_of_file -> !time

let legacy_parser_available executable =
  let log = Util.open_dummy_log () in
  let env = Unix.environment () in
  match
    Util.exec ~executable ~timeout:1.0 ~env ~log ~args:["-legacy-parser-available"] ()
  with
  | Util.Exit(0,_,_) -> true
  | _ -> false

let () = Runner.declare
  ~applicable:begin fun ~executable { Test.source_elpi; legacy_parser; _ } ->
    if is_elpi executable && source_elpi <> None && 
      (not legacy_parser || legacy_parser_available executable)
      then Runner.Can_run_it
    else Runner.Not_for_me
  end
  ~run:begin fun ~executable ~timetool ~timeout ~env ~sources test ->
  let source =
    match test.Test.source_elpi with Some x -> x | _ -> assert false in
  if not (Sys.file_exists executable) then Runner.Skipped
  else if not (Sys.file_exists (sources^source)) then Runner.Skipped
  else
    let log = Util.open_log ~executable test in
    Util.write log (Printf.sprintf "executable: %s\n" executable);
    let executable_stuff = Filename.dirname executable ^ "/../lib/elpi/" in

    let { Test.expectation; input; outside_llam ; typecheck; trace; legacy_parser; _ } = test in
    let input = Util.option_map (fun x -> sources^x) input in
    let args = ["-test";"-I";executable_stuff;"-I";sources;source] @ trace in
    let args =
      if typecheck then args
      else "-no-tc" :: args in
    let args =
      if not legacy_parser then args
      else "-legacy-parser" :: args in
    let args =
      if outside_llam then "-delay-problems-outside-pattern-fragment"::args
      else args in
    Util.write log (Printf.sprintf "args: %s\n" (String.concat " " args));

    let rc =
      let outcome = Util.exec ~timeout ~timetool ~close_output:false ?input ~executable ~env ~log ~args () in
      let typechecking = Util.with_log log read_tctime in
      let execution = Util.with_log log read_time in

      match outcome with
      | Util.Exit(0,walltime,mem) ->
        begin match expectation with
        | Test.Success -> Runner.Success { walltime; typechecking; execution; mem }
        | Test.SuccessOutput rex when Util.with_log log (match_rex rex) -> Runner.Success { walltime; typechecking; execution; mem }
        | Test.SuccessOutputFile { sample; adjust; reference } when match_file ~log sample adjust (sources^"/"^reference) -> Runner.Success { walltime; typechecking; execution; mem }
        | _ -> Runner.Failure { walltime; typechecking; execution; mem }
        end

      | Util.Exit(_,walltime,mem) ->
        begin match expectation with
        | Test.Failure -> Runner.Success { walltime; typechecking; execution; mem }
        | Test.FailureOutput rex when Util.with_log log (match_rex rex) -> Runner.Success { walltime; typechecking; execution; mem }
        | _ -> Runner.Failure { walltime; typechecking; execution; mem }
        end

      | Util.Timeout -> Runner.Timeout timeout
        
    in
    Util.close_log log;
    Runner.(Done { Runner.rc; executable; test; log = snd log })
  end

end

let match_rex rex input_line =
  let b = ref false in
  try while true do
    let l = input_line () in
    try ignore(Str.search_forward rex l 0); b := true
    with Not_found -> ()
  done; !b
  with End_of_file -> !b

module ElpiTraceElab = struct
  let is_elpi_elab =
    let rex = Str.regexp "elpi-trace-elaborator" in
    fun s -> Str.string_match rex (Filename.basename s) 0
  
  let () = Runner.declare
    ~applicable:(fun ~executable { Test.source_json; } ->
      if is_elpi_elab executable && source_json <> None then
        Runner.Can_run_it
      else Runner.Not_for_me)
    ~run:(fun ~executable ~timetool ~timeout ~env ~sources test ->
    if not (Sys.file_exists executable) then Runner.Skipped
    else
      let log = Util.open_log ~executable test in
      Util.write log (Printf.sprintf "executable: %s\n" executable);
      let source =
        match test.Test.source_json with Some x -> x | _ -> assert false in
      let input = sources ^ source in
      Util.write log (Printf.sprintf "input: %s\n" input);
      let outcome, outcomey =
        match test.Test.expectation with
        | Test.SuccessOutputFile { sample } ->
            let output_file = Util.open_file_w sample, sample in
            let output_file_tmp = Util.open_dummy_log () in
            Util.write log (Printf.sprintf "output: %s\n" (snd output_file));
            let outcome = Util.exec ~timeout ~timetool ~input ~executable ~env ~error:log ~log:output_file_tmp ~args:[] () in
            let outcomey = Some (Util.exec ~timeout ~timetool ~input:(snd output_file_tmp) ~executable:"ydump" ~env ~log:output_file ~args:[] ()) in
            outcome, outcomey
        | Test.FailureOutput _ ->
            let outcome = Util.exec ~timeout ~timetool ~input ~executable ~env ~log ~close_output:false ~args:[] () in
            outcome, None
        | _ -> Printf.eprintf "ElpiTraceElab only supoprts SuccessOutputFile / FailureOutput tests"; exit 1 in
      let typechecking = 0.0 in
      let execution = 0.0 in
      let rc =
        match outcome, outcomey, test.Test.expectation with
        | Util.Exit(0,walltime,mem), Some(Util.Exit(0,_,_)), Test.SuccessOutputFile { sample; adjust; reference } when match_file ~log sample adjust (sources^"/"^reference) ->
            Runner.Success { walltime; typechecking; execution; mem }
        | Util.Exit(m,walltime,mem), None, Test.FailureOutput rex when m != 0 && Util.with_log log (match_rex rex) ->
            Runner.Success { walltime; typechecking; execution; mem }
        | _ -> Runner.Failure { walltime = 0.0; typechecking; execution = 0.0; mem = 0 }
      in
      Util.close_log log;
      Runner.(Done { Runner.rc; executable; test; log = snd log })
      )

end

module Teyjus = struct

let assert_ok = function
  | Util.Exit(0,_,_) -> ()
  | _ -> failwith "error compiling test"
  
let is_tjsim =
  let rex = Str.regexp "tjsim" in
  fun s -> Str.string_match rex (Filename.basename s) 0

  let () = Runner.declare
  ~applicable:begin fun ~executable { Test.source_teyjus; _ } ->
    if is_tjsim executable && source_teyjus <> None then Runner.Can_run_it
    else Runner.Not_for_me
  end
  ~run:begin fun ~executable ~timetool ~timeout ~env ~sources test ->
  let source =
    match test.Test.source_teyjus with Some x -> sources^x | _ -> assert false in
  if not (Sys.file_exists executable) then Runner.Skipped
  else if not (Sys.file_exists source) then Runner.Skipped
  else
    let log = Util.open_log ~executable test in

    let { Test.expectation; input; _ } = test in
    let input = Util.option_map (fun x -> sources^x) input in

    let tjcc = Filename.dirname executable ^ "/tjcc" in
    let tjlink = Filename.dirname executable ^ "/tjlink" in

    let do1 cmd src =
      let dir = Filename.dirname src in
      let source = Filename.basename src in
      let modname = Filename.chop_extension source in
      let args = [modname] in
      let old = Unix.getcwd () in
      Unix.chdir dir;
      Util.write log (Printf.sprintf "%s %s\n" cmd modname);
      let rc = Util.exec ~timeout ~executable:cmd ~env ~log ~args ~close_output:false () in
      assert_ok rc;
      Unix.chdir old;
      dir, modname in

    List.iter (fun x -> ignore (do1 tjcc (sources^x)))
      test.Test.deps_teyjus;
    let _ = do1 tjcc source in

    let dir, modname = do1 tjlink source in

    let args = ["-m";"1";"-b";"-s";"main.";"-p";dir^"/";modname] in

    Util.write log (Printf.sprintf "%s %s\n" executable (String.concat " " args));
    let outcome = Util.exec ~timeout ~timetool ~executable ?input ~env ~log ~args ~close_output:false () in
    let typechecking = 0.0 in
    let rc =

      match outcome with
      | Util.Exit(0,walltime,mem) -> let execution = walltime in
        begin match expectation with
        | Test.Success -> Runner.Success { walltime; typechecking; execution; mem }
        | _ -> Runner.Failure { walltime; typechecking; execution; mem }
        end

      | Util.Exit(_,walltime,mem) -> let execution = walltime in
        begin match expectation with
        | Test.Failure -> Runner.Success { walltime; typechecking; execution; mem }
        | _ -> Runner.Failure { walltime; typechecking; execution; mem }
        end

      | Util.Timeout -> Runner.Timeout timeout

    in
    Runner.Done { Runner.rc; executable; test; log = snd log }
  end

end

module Dune = struct

let is_dune =
  let rex = Str.regexp "dune" in
  fun s -> Str.string_match rex (Filename.basename s) 0

let is_dune_src = function
  | None -> false
  | Some s -> Filename.check_suffix s ".ml"

let () = Runner.declare
  ~applicable:begin fun ~executable { source_dune; _ } ->
    if is_dune executable && is_dune_src source_dune then Runner.Can_run_it else Runner.Not_for_me
  end
  ~run:begin fun ~executable ~timetool ~timeout ~env ~sources test ->
  let source =
    match test.Test.source_dune with Some x -> x | _ -> assert false in
  if not (Sys.file_exists executable) then Runner.Skipped
  else if not (Sys.file_exists (sources^source)) then Runner.Skipped
  else
    let log = Util.open_log ~executable test in
    Util.write log (Printf.sprintf "executable: %s\n" executable);
    let { Test.expectation; input; outside_llam = _ ; typecheck = _; _ } = test in
    let sources = Str.global_replace (Str.regexp "^.*tests/sources/") "tests/sources/" sources in
    let source = Filename.remove_extension source ^ ".exe" in
    let args = ["exec"; sources ^ "/" ^ source; "--"; "-I"; "src/"] in
    Util.write log (Printf.sprintf "args: %s\n" (String.concat " " args));
    let rc =
      let outcome = Util.exec ~timeout ~timetool ?input ~executable ~env ~log ~args () in
      let typechecking = 0.0 in
      match outcome with
      | Util.Exit(0,walltime,mem) -> let execution = walltime in
        begin match expectation with
        | Test.Success -> Runner.Success { walltime; typechecking; execution; mem }
        | Test.SuccessOutput rex when Util.with_log log (match_rex rex) -> Runner.Success { walltime; typechecking; execution; mem }
        | _ -> Runner.Failure { walltime; typechecking; execution; mem }
        end

      | Util.Exit(_,walltime,mem) -> let execution = walltime in
        begin match expectation with
        | Test.Failure -> Runner.Success { walltime; typechecking; execution; mem }
        | Test.FailureOutput rex when Util.with_log log (match_rex rex) -> Runner.Success { walltime; typechecking; execution; mem }
        | _ -> Runner.Failure { walltime; typechecking; execution; mem }
        end

      | Util.Timeout -> Runner.Timeout timeout

    in
    Runner.(Done { Runner.rc; executable; test; log = snd log })

  end

end
