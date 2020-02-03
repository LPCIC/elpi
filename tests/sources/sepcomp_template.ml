open Elpi.API

let init () =
  let elpi, rest =
    Setup.init ~builtins:[Elpi.Builtin.std_builtins] ~basedir:"." (List.tl (Array.to_list Sys.argv)) in
  assert(rest = []);
  elpi

let cc ~elpi ~flags i u =
  Compile.unit ~elpi ~flags
    (Parse.program_from_stream ~elpi (Ast.Loc.initial (Printf.sprintf "<u%d>" i))
      (Stream.of_string u))

let link ~elpi us =
  let p = Compile.assemble ~elpi us in
  let q = Compile.query p (Parse.goal_from_stream (Ast.Loc.initial "g") (Stream.of_string "main")) in
  q

let check q =
  if not (Compile.static_check ~checker:(Elpi.Builtin.default_checker ()) q) then exit 1

let exec q =
    let exe = Compile.optimize q in
    match Execute.once exe with
    | Execute.Failure -> exit 1
    | Execute.Success _ -> exit 0
    | Execute.NoMoreSteps -> assert false

let main us =
  let elpi = init () in
  let flags = Compile.default_flags in
  let us = List.mapi (cc ~elpi ~flags) us in
  let q = link ~elpi us in
  check q;
  exec q
