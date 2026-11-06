(* Plugins: accumulate "+pkg" (the plugin of a package) and "+pkg/path" (a
   file of a package), with a host that knows the directory of the packages
   in tests/sources/plugins and loads some plugins on demand *)
open Elpi.API
open RawData

let dir = Filename.concat (Sys.getcwd ()) "tests/sources/plugins"

(* a plugin linked statically *)
let _ =
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInPredicate.Notation in
  Plugin.register ~name:"elpi-test.static" [
    MLCode(Pred("static.answer", Out(BuiltInData.int, "N", Easy "N is 42"),
      (fun _ ~depth:_ -> !: 42)), DocAbove);
  ]

(* plugins loaded on demand, after Setup.init *)
type shape = Circle of int | Square

let late () =
  let boxc = Constants.declare_global_symbol "box" in
  let shape = AlgebraicData.(declare {
    ty = Conversion.TyName "shape";
    doc = "a shape";
    pp = (fun fmt -> function Circle r -> Format.fprintf fmt "circle %d" r | Square -> Format.fprintf fmt "square");
    constructors = [
      K("circle", "a circle", A(BuiltInData.int, N),
        B (fun r -> Circle r), M (fun ~ok ~ko -> function Circle r -> ok r | _ -> ko ()));
      K("square", "a square", N,
        B Square, M (fun ~ok ~ko -> function Square -> ok | _ -> ko ()));
    ];
  }) |> ContextualConversion.(!<) in
  let twice = Calc.{ symbol = "twice"; infix = false; args = [["int"; "int"]];
    code = (function
      | [x] ->
          (match look ~depth:0 x with
           | CData d when RawOpaqueData.is_int d -> RawOpaqueData.of_int (2 * RawOpaqueData.to_int d)
           | _ -> Error.error "twice: not an int")
      | _ -> Error.error "twice: one argument") } in
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInPredicate.Notation in
  let open ContextualConversion in
  ignore @@ Plugin.register ~name:"elpi-test.late" [
    MLData shape;
    MLCalc (Calc.operations [twice]);
    LPCode "data box. symb box : int -> box.";
    MLConstants [boxc];
    MLCode(Pred("late.mk-box",
      In(BuiltInData.int, "N", Out(BuiltInData.any, "B", Full(unit_ctx, "B is box N"))),
      (fun n _ ~depth:_ _ _ state -> state, !: (mkApp boxc (RawOpaqueData.of_int n) []), [])),
    DocAbove);
    MLCode(Pred("late.area",
      In(shape, "S", Out(BuiltInData.int, "A", Easy "A is the area of S")),
      (fun s _ ~depth:_ -> !: (match s with Circle r -> 3 * r * r | Square -> 1))),
    DocAbove);
  ]

let load = function
  | "elpi-test.late" -> late ()
  | "elpi-test.stateful" ->
      ignore (State.declare_component ~name:"elpi-test:late" ~pp:(fun _ _ -> ())
        ~init:(fun () -> 0) ~start:(fun x -> x) ());
      ignore @@ Plugin.register ~name:"elpi-test.stateful" []
  | "elpi-test.lazy" -> () (* it does not register its plugin *)
  | p -> failwith ("no package " ^ p)

let package_dir = function
  | "elpi-test" | "elpi-test.stub" -> dir
  | p -> failwith ("no package " ^ p)

let with_load = { Setup.dir = package_dir; load = Some load }
let dir_only = { Setup.dir = package_dir; load = None }

(* the output of main, or the first error *)
let run ?packages ?(stubs=false) name text =
  let elpi = Setup.init ~builtins:[Elpi.Builtin.std_builtins]
    ~file_resolver:(Parse.std_resolver ~paths:[] ()) ?packages () in
  let flags = { Compile.default_flags with Compile.builtin_stubs = stubs } in
  let first_error = function e :: _ -> Some (Format.asprintf "%a" Error.pp_message e) | [] -> None in
  match Parse.program_from ~flags ~elpi ~loc:(Ast.Loc.initial (Filename.concat dir (name ^ ".elpi")))
          ~digest:(Digest.string text) (Lexing.from_string text) with
  | exception Parse.ParseError (_, msg) -> msg
  | _, errors, _ when Option.is_some (first_error errors) -> Option.get (first_error errors)
  | ast, _, _ ->
      match Compile.program ~flags ~elpi ast with
      | exception Error.ElpiError e -> Format.asprintf "%a" Error.pp_message e
      | _, errors, _ when Option.is_some (first_error errors) -> Option.get (first_error errors)
      | p, _, _ ->
          let goal = match Parse.query ~elpi ~loc:(Ast.Loc.initial "g") ~text:"main" with
            | Ok g, _ -> g | Error _, _ -> assert false in
          match Compile.query p goal with
          | Error e, _ -> Format.asprintf "%a" Error.pp_message e
          | Ok q, _ ->
              let buf = Buffer.create 80 in
              let fmt = Format.formatter_of_buffer buf in
              Setup.set_std_formatter fmt;
              let r = Execute.once (Compile.optimize q) in
              Format.pp_print_flush fmt ();
              match r with
              | Execute.Success _ -> String.trim (Buffer.contents buf)
              | _ -> "main failed"

(* separate compilation: the unit of a plugin, marshaled and read back *)
let sepcomp () =
  let elpi = Setup.init ~builtins:[Elpi.Builtin.std_builtins]
    ~file_resolver:(Parse.std_resolver ~paths:[] ()) () in
  let text = {| accumulate "+elpi-test.static". main :- static.answer N, print "sepcomp" N. |} in
  let ast, _, _ = Parse.program_from ~elpi ~loc:(Ast.Loc.initial (Filename.concat dir "sepcomp.elpi"))
    ~digest:(Digest.string text) (Lexing.from_string text) in
  let scoped, _, _ = Compile.scope_ast ~elpi ast in
  let names = List.map Compile.scoped_program_name scoped in
  let base = List.fold_left (fun base sp ->
      let u, _, _ = Compile.unit ~elpi ~base sp in
      let u : Compile.compilation_unit = Marshal.from_string (Marshal.to_string u []) 0 in
      let base, _, _ = Compile.extend ~base u in
      base) (Compile.empty_base ~elpi) scoped in
  let goal = match Parse.query ~elpi ~loc:(Ast.Loc.initial "g") ~text:"main" with
    | Ok g, _ -> g | Error _, _ -> assert false in
  match Compile.query base goal with
  | Error e, _ -> Format.asprintf "%a" Error.pp_message e
  | Ok q, _ ->
      let buf = Buffer.create 80 in
      let fmt = Format.formatter_of_buffer buf in
      Setup.set_std_formatter fmt;
      ignore (Execute.once (Compile.optimize q));
      Format.pp_print_flush fmt ();
      String.concat " " names ^ " | " ^ String.trim (Buffer.contents buf)

let failures = ref 0
let check name ~expect got =
  let rex = Str.regexp_string expect in
  let ok = try ignore (Str.search_forward rex got 0); true with Not_found -> false in
  if not ok then incr failures;
  Printf.printf "%s %s: %s\n" (if ok then "ok" else "KO") name got

let () =
  check "static" ~expect:"42"
    (run "static" {| accumulate "+elpi-test.static". main :- static.answer N, print N. |});
  check "static without packages" ~expect:"42"
    (run ~packages:dir_only "static2" {| accumulate "+elpi-test.static". main :- static.answer N, print N. |});
  check "on demand" ~expect:"3 12 43"
    (run ~packages:with_load "late" {|
      accumulate "+elpi-test.late".
      main :- late.mk-box 3 B, B = box N, late.area (circle 2) A, T is twice 21 + 1, print N A T. |});
  check "package file" ~expect:"14"
    (run ~packages:dir_only "file" {| accumulate "+elpi-test/util". main :- util.double 7 X, print X. |});
  check "plus path" ~expect:"7"
    (run "plus" {| accumulate "./+x". main :- plusfile X, print X. |});
  check "no packages" ~expect:"packages are disabled"
    (run "nopkg" {| accumulate "+elpi-test/util". main. |});
  check "missing" ~expect:"plugin elpi-test.missing is not available: no package elpi-test.missing"
    (run ~packages:with_load "missing" {| accumulate "+elpi-test.missing". main. |});
  check "not registered" ~expect:"package elpi-test.lazy did not register its plugin"
    (run ~packages:with_load "lazy" {| accumulate "+elpi-test.lazy". main. |});
  check "state component" ~expect:"plugin elpi-test.stateful declares state components: it must be loaded before Setup.init"
    (run ~packages:with_load "stateful" {| accumulate "+elpi-test.stateful". main. |});
  check "stub with builtin_stubs" ~expect:"stub ok"
    (run ~packages:dir_only ~stubs:true "stub" {| accumulate "+elpi-test.stub". main :- print "stub ok". |});
  check "stub without builtin_stubs" ~expect:"stub.f is declared builtin but no MLCode implements it"
    (run ~packages:dir_only "stub2" {| accumulate "+elpi-test.stub". main. |});
  check "separate compilation" ~expect:"+elpi-test.static " (sepcomp ());
  check "separate compilation runs" ~expect:"sepcomp 42" (sepcomp ());
  if !failures > 0 then exit 1;
  print_endline "all plugin cases ok"
