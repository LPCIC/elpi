(* A minimal Elpi embedding: registers one custom builtin (sys.file_exists,
   literalinclude'd from src/builtin.ml below) alongside the standard
   library, then parses, compiles and runs a program's main goal. *)

module E = Elpi.API

let my_builtins =
  let open E.BuiltIn in
  let open E.BuiltInPredicate in
  let open E.BuiltInData in
  declare ~file_name:"my_builtins.elpi" [
    MLCode (Pred ("sys.file_exists",
      In (string, "Path",
      Easy "succeeds if the file at Path exists"),
    (fun path ~depth:_ ->
      if Sys.file_exists path then () else raise No_clause)),
    DocAbove);
  ]

let () =
  let elpi =
    E.Setup.init
      ~builtins:[Elpi.Builtin.std_builtins; my_builtins]
      ~file_resolver:(E.Parse.std_resolver ~paths:[] ())
      () in
  let program = E.Parse.program ~elpi ~file:"my_program.elpi" in
  let goal = E.Parse.goal ~elpi ~loc:(E.Ast.Loc.initial "cli") ~text:"main." in
  let prog = E.Compile.program ~flags:E.Compile.default_flags ~elpi program in
  let executable = E.Compile.optimize (E.Compile.query prog goal) in
  match E.Execute.once executable with
  | E.Execute.Success _ -> print_endline "Success"
  | E.Execute.Failure -> print_endline "Failure"
  | E.Execute.NoMoreSteps -> print_endline "NoMoreSteps"
