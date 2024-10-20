open Elpi.API

let init () =
  Setup.init ~builtins:[Elpi.Builtin.std_builtins] ~file_resolver:(Parse.std_resolver ~paths:[] ()) ()

let cc ~elpi ~flags ~base i u =
  let u =
    Compile.unit ~elpi ~flags ~base
      (Parse.program_from ~elpi ~loc:(Ast.Loc.initial (Printf.sprintf "<u%d>" i))
        (Lexing.from_string u)) in
  Compile.extend ~flags ~base u, u


let check q =
  ()
  (* if not (Compile.static_check ~checker:(Elpi.Builtin.default_checker ()) q) then exit 1 *)

  
let query ~elpi p =
  Compile.query p
    (Parse.goal_from ~elpi ~loc:(Ast.Loc.initial "g") (Lexing.from_string "main"))

let exec q =
    let exe = Compile.optimize q in
    match Execute.once exe with
    | Execute.Failure -> exit 1
    | Execute.Success _ -> exit 0
    | Execute.NoMoreSteps -> assert false

let main us =
  let elpi = init () in
  let flags = Compile.default_flags in
  let base = Compile.empty_base ~elpi in
  let _,p = List.fold_left (fun (i,base) u -> i+1,fst @@ cc ~elpi ~flags ~base i u) (0,base) us in
  let q = query ~elpi p in
  exec q
