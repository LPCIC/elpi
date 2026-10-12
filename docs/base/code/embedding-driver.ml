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
        E.Utils.error ("file_exists: " ^ e))),
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
  let program, errors = E.Parse.program ~flags ~elpi "my_program.elpi" in
  List.iter (fun e -> Format.eprintf "%a@." E.Compile.pp_error e) errors;
  if errors <> [] then exit 1;
  let goal = E.Parse.goal ~elpi ~loc:(E.Ast.Loc.initial "cli") ~text:"main." in
  let prog, errors = E.Compile.program ~flags ~elpi program in
  List.iter (fun e -> Format.eprintf "%a@." E.Compile.pp_error e) errors;
  if errors <> [] then exit 1;
  let executable = E.Compile.optimize (E.Compile.query prog goal) in
  match E.Execute.once executable with
  | E.Execute.Success _ -> print_endline "Success"
  | E.Execute.Failure -> print_endline "Failure"
  | E.Execute.NoMoreSteps -> print_endline "NoMoreSteps"
