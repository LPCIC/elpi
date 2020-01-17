open Elpi.API

let init () =
  let header, rest =
    Setup.init ~builtins:Elpi.Builtin.std_builtins ~basedir:"." (List.tl (Array.to_list Sys.argv)) in
  assert(rest = []);
  header

let cc ~flags i u =
  Compile.unit ~flags
    (Parse.program_from_stream (Ast.Loc.initial (Printf.sprintf "<u%d>" i))
      (Stream.of_string u))

let link ~flags header us =
  let p = Compile.assemble ~flags header us in
  let q = Compile.query p (Parse.goal_from_stream (Ast.Loc.initial "g") (Stream.of_string "main")) in
  q

let check header ~flags q =
  if not (Compile.static_check header ~flags q) then exit 1

let exec ~flags q =
    let exe = Compile.link ~flags q in
    match Execute.once exe with
    | Execute.Failure -> exit 1
    | Execute.Success _ -> exit 0
    | Execute.NoMoreSteps -> assert false

let main us =
  let header = init () in
  let flags = Compile.default_flags in
  let us = List.mapi (cc ~flags) us in
  let q = link ~flags header us in
  check ~flags header q;
  exec ~flags q
