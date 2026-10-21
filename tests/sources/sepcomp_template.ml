open Elpi.API

let init () =
  Setup.init ~builtins:[Elpi.Builtin.std_builtins] ~file_resolver:(Parse.std_resolver ~paths:[] ()) ()

(* the result of a pass, after checking that it found no error; the warnings
   are printed *)
let ok (x, errors, warnings) =
  List.iter (fun { Error.warning = e } -> Format.eprintf "Warning: %a@." Error.pp e) warnings;
  List.iter (fun e -> Format.eprintf "%a@." Error.pp e) errors;
  if errors <> [] then exit 1;
  x

let cc ~elpi ~flags ~base i u =
  let u =
    ok @@ Compile.unit ~elpi ~flags ~base
    (match
     ok @@ (Compile.scope_ast ~elpi ~flags
      (ok (Parse.program_from ~elpi ~digest:(Digest.string u) ~loc:(Ast.Loc.initial (Printf.sprintf "<u%d>" i))
        (Lexing.from_string u))))
    with [x] -> x | _ -> assert false) in
  ok (Compile.extend ~flags ~base u), u

let signature_of u = Compile.signature u

let extend ~flags ~base u = ok (Compile.extend ~flags ~base u)
let extend_signature ~flags ~base u = ok (Compile.extend_signature ~flags ~base u)

let check q =
  ()
  (* if not (Compile.static_check ~checker:(Elpi.Builtin.default_checker ()) q) then exit 1 *)

  
(* the compiled query, after checking that it has no error *)
let ok_query (q, warnings) =
  List.iter (fun { Error.warning = e } -> Format.eprintf "Warning: %a@." Error.pp e) warnings;
  match q with
  | Ok q -> q
  | Error e -> Format.eprintf "%a@." Error.pp e; exit 1

(* the parsed query, after checking that it has no error *)
let ok_goal ~elpi text = ok_query (Parse.query ~elpi ~loc:(Ast.Loc.initial "g") ~text)

let query ~elpi p =
  ok_query @@ Compile.query p (ok_goal ~elpi "main")

let exec q =
    let exe = Compile.optimize q in
    match Execute.once exe with
    | Execute.Failure -> exit 1
    | Execute.Success _ -> exit 0
    | Execute.NoMoreSteps -> assert false

let try_exec q =
    let exe = Compile.optimize q in
    match Execute.once exe with
    | Execute.Failure -> false
    | Execute.Success _ -> true
    | Execute.NoMoreSteps -> assert false
    
let main us =
  let elpi = init () in
  let flags = Compile.default_flags in
  let base = Compile.empty_base ~elpi in
  let _,p = List.fold_left (fun (i,base) u -> i+1,fst @@ cc ~elpi ~flags ~base i u) (0,base) us in
  let q = query ~elpi p in
  exec q
