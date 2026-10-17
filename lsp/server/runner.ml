(* Running a query on a program, for the request elpi/run: the result, as
   JSON, is
   { status: "success" | "failure" | "error", output: string,
     errors: [string], diagnostics: [string] }
   - status: "success" if the query succeeds, "failure" if it fails, "error" if
     the query has syntax or type errors, if running it raises an error, or if
     the program cannot be compiled at all. A program with errors is run
     anyway, without the declarations and rules that have errors;
   - output: what the program printed;
   - diagnostics: the errors and the warnings of the program, each with its
     location: what the server publishes as the diagnostics of the document,
     so a client that shows those (e.g. an editor) needs not show them again;
   - errors: the rest, i.e. the errors and the warnings of the query and of
     its run (e.g. "no more steps"), and last, if the program has errors, a
     warning that it could not be fully compiled, with the number of its
     errors (they are in diagnostics). *)

open Elpi.API

let show_loc = function
  | None -> ""
  | Some loc -> Format.asprintf "%a@\n" Ast.Loc.pp loc

let show_exn e =
  let loc, msg = Checker.error_of_exn e in
  show_loc loc ^ msg

(* [run ?max_steps ~path ~text ~query] parses and compiles [text] (the file
   [path], for the locations and accumulate), then runs [query] (a final dot is
   optional) once, for at most [max_steps] steps of the interpreter (then the
   status is failure, with the error "no more steps") *)
let run ?max_steps ~path ~text ~query () : Yojson.Safe.t =
  let output = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer output in
  let outer_warnings = !Checker.warnings in
  Checker.warnings := [];
  (* the warnings emitted since the last call *)
  let take_warnings () =
    let ws = List.rev_map (fun (loc, msg) -> show_loc loc ^ "Warning: " ^ msg) !Checker.warnings in
    Checker.warnings := [];
    ws in
  Setup.set_std_formatter fmt;
  let status, diagnostics, errors =
    Fun.protect ~finally:(fun () ->
        Format.pp_print_flush fmt ();
        Setup.set_std_formatter Format.err_formatter) @@ fun () ->
    (* the program: its errors and warnings are diagnostics. The passes are
       error resilient: a program with errors is compiled without the
       declarations and rules that have errors, and can be run *)
    let program =
      try
        let elpi = Lazy.force Checker.elpi in
        let flags = { Compile.default_flags with Compile.max_errors = !Checker.max_errors } in
        let ast, parse_errors =
          Parse.program_from ~flags ~elpi ~loc:(Ast.Loc.initial path) ~digest:(Digest.string text)
            (Lexing.from_string text) in
        let program, compile_errors = Compile.program ~flags ~elpi ast in
        Ok (elpi, program, List.map Compile.show_error (parse_errors @ compile_errors))
      with e -> Error [ show_exn e ] in
    let program_warnings = take_warnings () in
    match program with
    | Error errors -> "error", program_warnings @ errors, []
    | Ok (elpi, program, program_errors) ->
        (* the output says that what was run is not the whole program *)
        let incomplete =
          match List.length program_errors with
          | 0 -> []
          | 1 -> [ "Warning: the program could not be fully compiled: 1 error" ]
          | n -> [ Printf.sprintf "Warning: the program could not be fully compiled: %d errors" n ] in
        (* the query and its run: their errors and warnings are errors *)
        let status, errors =
          try
            let query = String.trim query in
            let query = if query <> "" && query.[String.length query - 1] = '.' then query else query ^ "." in
            let goal = Parse.goal ~elpi ~loc:(Ast.Loc.initial "(query)") ~text:query in
            let exe = Compile.optimize (Compile.query program goal) in
            match Execute.once ?max_steps exe with
            | Execute.Success _ -> "success", []
            | Failure -> "failure", []
            | NoMoreSteps -> "failure", [ "no more steps" ]
          with e -> "error", [ show_exn e ] in
        status, program_warnings @ program_errors, take_warnings () @ errors @ incomplete in
  Checker.warnings := outer_warnings;
  let strings l = `List (List.map (fun s -> `String s) l) in
  `Assoc [
    "status", `String status;
    "output", `String (Buffer.contents output);
    "errors", strings errors;
    "diagnostics", strings diagnostics;
  ]
