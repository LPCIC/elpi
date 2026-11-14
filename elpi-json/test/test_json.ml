(* the plugin elpi-json, linked statically, and its utilities, found in
   the directory of the sources as the directory of package elpi-json *)
open Elpi.API

let program = {|
accumulate "+elpi-json/utils".
main :-
  json.from_string "{ \"name\": \"elpi\", \"tags\": [1, 2] }" J ok,
  json.lookup J "tags" T, print T,
  json.to_string J S ok, print S.
|}

let () =
  ignore Elpi_json.builtins;
  let dir = Sys.argv.(1) in
  let packages = { Setup.dir = (fun ~pkg -> match pkg with "elpi-json" -> dir | p -> Error.error ("no package " ^ p)); load = None;
    root_of_dir = (fun ~dir:_ -> dir) } in
  let elpi = Setup.init ~builtins:[Elpi.Builtin.std_builtins] ~file_resolver:(Parse.std_resolver ~paths:[] ()) ~packages () in
  let ast, _, _ = Parse.program_from ~elpi ~loc:(Ast.Loc.initial "test.elpi") ~digest:(Digest.string program) (Lexing.from_string program) in
  let p, _, _ = Compile.program ~elpi ast in
  let goal = match Parse.query ~elpi ~loc:(Ast.Loc.initial "g") ~text:"main" with Ok g, _ -> g | Error _, _ -> exit 1 in
  match Compile.query p goal with
  | Error e, _ -> Format.eprintf "%a@." Error.pp e; exit 1
  | Ok q, _ ->
      match Execute.once (Compile.optimize q) with
      | Execute.Success _ -> ()
      | _ -> exit 1
