(* A minimal Elpi embedding: registers one custom builtin (sys.file_exists,
   the same implementation as builtin.ml's own, shown above) alongside the
   standard library, then parses, compiles and runs a program's main goal. *)

module E = Elpi.API

let my_builtins =
  let open E.BuiltIn in
  let open E.BuiltInPredicate in
  let open E.BuiltInData in
  declare ~file_name:"my_builtins.elpi" [
    MLCode (Pred ("sys.file_exists",
      In  (string, "Path",
      Easy "is like [Sys.file_exists]. It succeeds if the file at [Path] exists"),
    (fun path ~depth:_ ->
      match Sys.file_exists path with
      | true -> ()
      | false -> raise No_clause
      | exception Sys_error e ->
        (* No recoverable errors are produced by Sys.file_exists *)
        E.Error.error ~component:"my_builtins" ("file_exists: " ^ e))),
    DocAbove);
  ]

let () =
  let elpi =
    E.Setup.init
      ~builtins:[Elpi.Builtin.std_builtins; my_builtins]
      ~file_resolver:(E.Parse.std_resolver ~paths:[] ())
      () in
  (* report up to 10 errors, instead of raising the first one *)
  let flags = { E.Compile.default_flags with E.Compile.max_errors = 10 } in
  let program, errors, warnings = E.Parse.program ~flags ~elpi "my_program.elpi" in
  List.iter (fun { E.Error.warning = e } -> Format.eprintf "Warning: %a@." E.Error.pp e) warnings;
  List.iter (fun e -> Format.eprintf "%a@." E.Error.pp e) errors;
  if errors <> [] then exit 1;
  let goal, warnings = E.Parse.query ~elpi ~loc:(E.Ast.Loc.initial "cli") ~text:"main." in
  List.iter (fun { E.Error.warning = e } -> Format.eprintf "Warning: %a@." E.Error.pp e) warnings;
  let goal = match goal with Ok g -> g | Error e -> Format.eprintf "%a@." E.Error.pp e; exit 1 in
  let prog, errors, warnings = E.Compile.program ~flags ~elpi program in
  List.iter (fun { E.Error.warning = e } -> Format.eprintf "Warning: %a@." E.Error.pp e) warnings;
  List.iter (fun e -> Format.eprintf "%a@." E.Error.pp e) errors;
  if errors <> [] then exit 1;
  let query, warnings = E.Compile.query prog goal in
  List.iter (fun { E.Error.warning = e } -> Format.eprintf "Warning: %a@." E.Error.pp e) warnings;
  let query = match query with Ok q -> q | Error e -> Format.eprintf "%a@." E.Error.pp e; exit 1 in
  let executable = E.Compile.optimize query in
  match E.Execute.once executable with
  | E.Execute.Success _ -> print_endline "Success"
  | E.Execute.Failure -> print_endline "Failure"
  | E.Execute.NoMoreSteps -> print_endline "NoMoreSteps"
