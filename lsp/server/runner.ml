(* Running a query on a program, for the request elpi/run: the result, as
   JSON, is
   { status: "success" | "failure" | "error", output: string,
     errors: [string], diagnostics: [string],
     assignments?: { [name]: string }, constraints?: [string] }
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
     errors (they are in diagnostics);
   - assignments: only on success, the value of each variable of the query;
   - constraints: only on success, the constraints left by the run, as the REPL
     prints them, e.g. "{c0} : hyps ?- goal /* suspended on X0 */". *)

open Elpi.API

let show_loc = function
  | None -> ""
  | Some loc -> Format.asprintf "%a@\n" Ast.Loc.pp loc

let show_exn e =
  let loc, msg = Checker.error_of_exn e in
  show_loc loc ^ msg

(* the warnings of the builtins at run time (see Builtin.set_runtime_warn):
   collected during a run (see run), logged outside a run *)
let log_runtime_warning ?loc ~id:_ msg = Checker.log "warning: %s%s" (show_loc loc) msg

(* [run ?max_steps ~instance ~path ~text ~query] parses and compiles [text]
   (the file [path], for the locations and accumulate) with [instance], then
   runs [query] (a final dot is
   optional) once, for at most [max_steps] steps of the interpreter (then the
   status is failure, with the error "no more steps") *)
let run ?max_steps ~instance ~path ~text ~query () : Yojson.Safe.t =
  let output = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer output in
  let show_warning { Error.warning = ({ loc } as e) } =
    show_loc loc ^ "Warning: " ^ Format.asprintf "%a" Error.pp_message e in
  (* the warnings of the run (of the builtins), most recent first *)
  let runtime_warnings = ref [] in
  Elpi.Builtin.set_runtime_warn (fun ?loc ~id:_ msg -> runtime_warnings := (loc, msg) :: !runtime_warnings);
  Setup.set_std_formatter fmt;
  (* the constraints left by a successful run, as the REPL prints them:
     [{c0 c1} : hyps ?- goal /* suspended on X0 */] *)
  let show_constraint pp_ctx state { RawData.context; goal = (depth, goal); blockers } =
    let term t = Format.asprintf "%a" (Pp.term pp_ctx) t in
    let terms l = String.concat ", " (List.map term l) in
    let eigen =
      if depth = 0 then ""
      else "{" ^ String.concat " " (List.init depth (fun i -> term (RawData.mkBound i))) ^ "} : " in
    let hyps = if context = [] then "" else terms (List.map (fun { RawData.hsrc } -> hsrc) context) ^ " ?- " in
    let blockers = terms (List.map (fun b -> RawData.mkUnifVar b ~args:[] state) blockers) in
    eigen ^ hyps ^ term goal ^ " /* suspended on " ^ blockers ^ " */" in
  let status, diagnostics, errors, solution =
    Fun.protect ~finally:(fun () ->
        Format.pp_print_flush fmt ();
        Setup.set_std_formatter Format.err_formatter;
        Elpi.Builtin.set_runtime_warn log_runtime_warning) @@ fun () ->
    (* the program: its errors and warnings are diagnostics. The passes are
       error resilient: a program with errors is compiled without the
       declarations and rules that have errors, and can be run *)
    let program =
      try
        let elpi = Checker.elpi instance in
        let flags = { Compile.default_flags with Compile.max_errors = !Checker.max_errors } in
        let ast, parse_errors, parse_warnings =
          Parse.program_from ~flags ~elpi ~loc:(Ast.Loc.initial path) ~digest:(Digest.string text)
            (Lexing.from_string text) in
        let program, compile_errors, compile_warnings = Compile.program ~flags ~elpi ast in
        Ok (elpi, program, List.map Error.show (parse_errors @ compile_errors),
            List.map show_warning (parse_warnings @ compile_warnings))
      with e -> Error [ show_exn e ] in
    match program with
    | Error errors -> "error", errors, [], None
    | Ok (elpi, program, program_errors, program_warnings) ->
        (* the output says that what was run is not the whole program *)
        let incomplete =
          match List.length program_errors with
          | 0 -> []
          | 1 -> [ "Warning: the program could not be fully compiled: 1 error" ]
          | n -> [ Printf.sprintf "Warning: the program could not be fully compiled: %d errors" n ] in
        (* the query and its run: their errors and warnings are errors *)
        let status, errors, solution =
          try
            let query = String.trim query in
            let query = if not (String.equal query "") && query.[String.length query - 1] = '.' then query else query ^ "." in
            let q, warnings =
              match Parse.query ~elpi ~loc:(Ast.Loc.initial "(query)") ~text:query with
              | Ok goal, parse_warnings ->
                  let q, warnings = Compile.query program goal in
                  q, parse_warnings @ warnings
              | Error e, parse_warnings -> Error e, parse_warnings in
            let warnings = List.map show_warning warnings in
            match q with
            | Error e -> "error", warnings @ [ Error.show e ], None
            | Ok q ->
                match Execute.once ?max_steps (Compile.optimize q) with
                | Execute.Success { Data.assignments; constraints; pp_ctx; state; _ } ->
                    let assignments = Data.StrMap.bindings assignments |> List.map (fun (name, t) ->
                        name, Format.asprintf "%a" (Pp.term pp_ctx) t) in
                    let constraints = List.map (show_constraint pp_ctx state) (RawData.constraints constraints) in
                    "success", warnings, Some (assignments, constraints)
                | Failure -> "failure", warnings, None
                | NoMoreSteps -> "failure", warnings @ [ "no more steps" ], None
          with e -> "error", [ show_exn e ], None in
        let runtime_warnings = List.rev_map (fun (loc, msg) -> show_loc loc ^ "Warning: " ^ msg) !runtime_warnings in
        status, program_warnings @ program_errors, runtime_warnings @ errors @ incomplete, solution in
  let strings l = `List (List.map (fun s -> `String s) l) in
  `Assoc ([
    "status", `String status;
    "output", `String (Buffer.contents output);
    "errors", strings errors;
    "diagnostics", strings diagnostics;
  ] @ (match solution with
      | Some (assignments, constraints) ->
          [ "assignments", `Assoc (List.map (fun (name, t) -> name, `String t) assignments);
            "constraints", strings constraints ]
      | None -> []))
