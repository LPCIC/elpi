(* Unit tests of Compiler_data.Errors, the collector of the errors of the
   resilient passes *)

open Elpi_compiler.Compiler_data
open Elpi_util.Util

let check name b = if not b then (Printf.eprintf "FAILED: %s\n" name; exit 1)

let loc n = Loc.{ (initial "test") with source_start = n; source_stop = n + 1 }

(* a unit of work that fails *)
let fail ?(component="A") n () =
  let ErrorFun { error } = error_fun ~component in
  error ~loc:(loc n) (Printf.sprintf "problem %d" n)

let () =
  (* a unit that works returns its result and records nothing *)
  let errs = Errors.make () in
  check "ok" (Errors.protect errs ~default:0 (fun () -> 42) = 42);
  check "no error" (Errors.list errs = [])

let () =
  (* a failing unit returns the default, and its error is recorded with the
     component and the location; errors are in order of occurrence *)
  let errs = Errors.make () in
  let r1 = Errors.protect errs ~default:"d1" (fail ~component:"Scope" 1) in
  let r2 = Errors.protect errs ~default:"d2" (fail ~component:"Typechecker" 2) in
  let r3 = Errors.protect errs ~default:"d3" (fun () -> "ok") in
  check "defaults" (String.equal r1 "d1" && String.equal r2 "d2" && String.equal r3 "ok");
  match Errors.list errs with
  | [ { component = "Scope"; loc = Some l1; message = "problem 1" };
      { component = "Typechecker"; loc = Some l2; message = "problem 2" } ] ->
      check "locations" (l1.Loc.source_start = 1 && l2.Loc.source_start = 2)
  | _ -> check "errors in order" false

let () =
  (* only ElpiError is caught: bugs propagate *)
  let errs = Errors.make () in
  check "Failure propagates"
    (match Errors.protect errs ~default:() (fun () -> failwith "bug") with
     | () -> false
     | exception Failure _ -> true);
  check "Not_found propagates"
    (match Errors.protect errs ~default:() (fun () -> raise Not_found) with
     | () -> false
     | exception Not_found -> true);
  check "nothing recorded for bugs" (Errors.list errs = [])

let () =
  (* after max_errors errors the other units are not run, and a final error
     says so, once *)
  let errs = Errors.make ~max_errors:2 () in
  let ran = ref 0 in
  for i = 1 to 5 do
    Errors.protect errs ~default:() (fun () -> incr ran; fail i ())
  done;
  check "units after the limit are not run" (!ran = 2);
  match Errors.list errs with
  | [ { message = "problem 1" }; { message = "problem 2" };
      { component = "Compiler"; loc = None; message } ] ->
      check "final error says why" (String.length message > 0 && String.equal (String.sub message 0 15) "too many errors")
  | l -> Printf.eprintf "%d errors\n" (List.length l); check "two errors and the final one" false

let () =
  (* no final error if nothing was skipped *)
  let errs = Errors.make ~max_errors:2 () in
  Errors.protect errs ~default:() (fail 1);
  Errors.protect errs ~default:() (fail 2);
  check "exactly the limit, nothing skipped" (List.length (Errors.list errs) = 2)

let () =
  (* printing: Component: message, with the location in front *)
  let e = { component = "Typechecker"; loc = Some (loc 7); message = "q is unknown" } in
  check "message" (String.equal (Format.asprintf "%a" pp_error_message e) "Typechecker: q is unknown");
  let full = show_error e in
  check "full" (String.length full > 0 && Re.Str.(string_match (regexp ".*\n.*Typechecker: q is unknown$") full 0));
  let e = { e with loc = None } in
  check "no location" (String.equal (show_error e) "Typechecker: q is unknown");
  (* first_error: the result or the first error, and the warnings *)
  let warn errs = Errors.warn errs ~component:"A" ~id:LinearVariable "w" in
  check "first_error ok" (match first_error (fun errs -> warn errs; 1) with Ok 1, [ _ ] -> true | _ -> false);
  match first_error (fun errs ->
      warn errs;
      Errors.protect errs ~default:() (fun () ->
        let ErrorFun { error } = error_fun ~component:e.component in
        error ?loc:e.loc e.message);
      Errors.protect errs ~default:() (fail 2)) with
  | Error e', [ { warning_id = LinearVariable } ] -> check "first_error error" (e' = e)
  | _ -> check "first_error" false

let () =
  (* max_errors = 0: the first error is raised, with its component *)
  let errs = Errors.make ~max_errors:0 () in
  check "0: ok" (Errors.protect errs ~default:0 (fun () -> 1) = 1);
  (match Errors.protect errs ~default:()
           (fun () -> Errors.protect errs ~default:() (fail ~component:"Inner" 3)) with
   | () -> check "0: raises" false
   | exception ElpiError { component = "Inner"; loc = Some l; message = "problem 3" } ->
       check "0: location" (l.Loc.source_start = 3));
  check "0: nothing collected" (Errors.list errs = [])

let () =
  (* an anomaly (a bug) of a component is an error of that component: it is
     recorded (and the unit dropped), or raised when max_errors = 0 *)
  let anomaly () =
    let ErrorFun { anomaly } = error_fun ~component:"A" in
    anomaly ~loc:(loc 7) "bug" in
  let errs = Errors.make () in
  check "anomaly: default" (Errors.protect errs ~default:1 anomaly = 1);
  check "anomaly recorded"
    (Errors.list errs = [ { component = "A"; loc = Some (loc 7); message = "anomaly: bug" } ]);
  let errs = Errors.make ~max_errors:0 () in
  check "anomaly raised"
    (match Errors.protect errs ~default:() anomaly with
     | () -> false
     | exception ElpiError { message = "anomaly: bug" } -> true)
