(* Plugins: accumulate "+pkg" (the plugin of a package) and "+pkg/path" (a
   file of a package), with a host that knows the directory of the packages
   in tests/sources/plugins and loads some plugins on demand *)
open Elpi.API
open RawData

let dir = Elpi.API.Utils.filename_concat (Sys.getcwd ()) "tests/sources/plugins"

(* a plugin linked statically *)
let _ =
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInPredicate.Notation in
  Plugin.register ~name:"test.static" [
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
  let twice = Calc.{ symbol = "twice"; infix = false; variant = ""; args = ["int"; "int"];
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
  ignore @@ Plugin.register ~name:"test.late" [
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

let load ~pkg = match pkg with
  | "test.late" -> late ()
  | "test.stateful" ->
      ignore (State.declare_component ~name:"test:late" ~pp:(fun _ _ -> ())
        ~init:(fun () -> 0) ~start:(fun x -> x) ());
      ignore @@ Plugin.register ~name:"test.stateful" []
  | "test.hoas" ->
      RawData.set_extra_goals_postprocessing (fun goals state -> state, goals);
      ignore @@ Plugin.register ~name:"test.hoas" []
  | "test.quot" ->
      ignore (Quotation.register_named_quotation ~name:"testq" (fun ~language:_ _ _ _ -> assert false));
      ignore @@ Plugin.register ~name:"test.quot" []
  | "test.lazy" -> () (* it does not register its plugin *)
  | p -> Error.error ("no package " ^ p)

let package_dir ~pkg = match pkg with
  | "test" | "test.stub" -> dir
  | p -> Error.error ("no package " ^ p)

(* "+/path": the files in tests/sources/plugins belong to package test *)
let root_of_dir ~dir:d =
  let n = String.length dir in
  if String.length d >= n && String.equal (String.sub d 0 n) dir then dir
  else Error.error ("no project contains " ^ d)

let with_load = { Setup.dir = package_dir; load = Some load; root_of_dir }
let dir_only = { Setup.dir = package_dir; load = None; root_of_dir }

(* the output of main, or the first error *)
let run ?packages ?(stubs=false) name text =
  let elpi = Setup.init ~builtins:[Elpi.Builtin.std_builtins]
    ~file_resolver:(Parse.std_resolver ~paths:[] ()) ?packages () in
  let flags = { Compile.default_flags with Compile.builtin_stubs = stubs } in
  let first_error = function e :: _ -> Some (Format.asprintf "%a" Error.pp_message e) | [] -> None in
  match Parse.program_from ~flags ~elpi ~loc:(Ast.Loc.initial (Elpi.API.Utils.filename_concat dir (name ^ ".elpi")))
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

(* the first parse error of a program, with the file of its location, in
   error resilient mode (as elpi-lsp) *)
let run_located ?packages name text =
  let elpi = Setup.init ~builtins:[Elpi.Builtin.std_builtins]
    ~file_resolver:(Parse.std_resolver ~paths:[] ()) ?packages () in
  let flags = { Compile.default_flags with Compile.max_errors = 5 } in
  match Parse.program_from ~flags ~elpi ~loc:(Ast.Loc.initial (Elpi.API.Utils.filename_concat dir (name ^ ".elpi")))
          ~digest:(Digest.string text) (Lexing.from_string text) with
  | exception e -> "exception " ^ Printexc.to_string e
  | _, { Error.loc = Some l; _ } :: _, _ -> "error in " ^ Filename.basename l.Ast.Loc.source_name
  | _, { Error.loc = None; message; _ } :: _, _ -> message
  | _, [], _ -> "no error"

(* separate compilation: the unit of a plugin, marshaled and read back *)
let sepcomp () =
  let elpi = Setup.init ~builtins:[Elpi.Builtin.std_builtins]
    ~file_resolver:(Parse.std_resolver ~paths:[] ()) () in
  let text = {| accumulate "+test.static". main :- static.answer N, print "sepcomp" N. |} in
  let ast, _, _ = Parse.program_from ~elpi ~loc:(Ast.Loc.initial (Elpi.API.Utils.filename_concat dir "sepcomp.elpi"))
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
    (run "static" {| accumulate "+test.static". main :- static.answer N, print N. |});
  check "static without packages" ~expect:"42"
    (run ~packages:dir_only "static2" {| accumulate "+test.static". main :- static.answer N, print N. |});
  check "on demand" ~expect:"3 12 43"
    (run ~packages:with_load "late" {|
      accumulate "+test.late".
      main :- late.mk-box 3 B, B = box N, late.area (circle 2) A, T is twice 21 + 1, print N A T. |});
  check "package file" ~expect:"14"
    (run ~packages:dir_only "file" {| accumulate "+test/util". main :- util.double 7 X, print X. |});
  check "current package" ~expect:"14"
    (run ~packages:dir_only "current" {| accumulate "+/util". main :- util.double 7 X, print X. |});
  check "current package in a subdirectory" ~expect:"28"
    (run ~packages:dir_only "deep" {| accumulate "sub/deep". main :- deep.quadruple 7 X, print X. |});
  (* a syntax error in a file of a package is an error of the program, not an
     exception: the unit of the file is named by its path *)
  check "syntax error in a package file" ~expect:"error in broken.elpi"
    (run_located ~packages:dir_only "broken" {| accumulate "+test/broken". main. |});
  (* a generated accumulate keeps UTF-8, quotes and backslashes (%S does
     not, for Elpi) *)
  let s = "jos\xc3\xa9 \"q\" a\\b" in
  check "string literal" ~expect:("[ " ^ s ^ " ]")
    (run "literal" (Printf.sprintf {| main :- X = %s, print "[" X "]". |} (Utils.string_literal s)));
  check "current package without packages" ~expect:"packages are disabled"
    (run "nocurrent" {| accumulate "+/util". main. |});
  check "no file" ~expect:"accumulate \"+test/\": no file after the package"
    (run ~packages:dir_only "nofile" {| accumulate "+test/". main. |});
  check "no package" ~expect:"no package after +"
    (run ~packages:dir_only "nopkgname" {| accumulate "+". main. |});
  (* two files with the same text in two directories: each resolves its own
     accumulates *)
  check "same text, two directories" ~expect:"[ 1 2 ]"
    (run "twin" {| accumulate "twin/a/t". accumulate "twin/b/t". main :- twin.a A, twin.b B, print "[" A B "]". |});
  check "plus path" ~expect:"7"
    (run "plus" {| accumulate "./+x". main :- plusfile X, print X. |});
  check "no packages" ~expect:"packages are disabled"
    (run "nopkg" {| accumulate "+test/util". main. |});
  check "missing" ~expect:"plugin test.missing is not available: no package test.missing"
    (run ~packages:with_load "missing" {| accumulate "+test.missing". main. |});
  check "not registered" ~expect:"package test.lazy did not register its plugin"
    (run ~packages:with_load "lazy" {| accumulate "+test.lazy". main. |});
  check "state component" ~expect:"plugin test.stateful declares state components: it must be loaded before Setup.init"
    (run ~packages:with_load "stateful" {| accumulate "+test.stateful". main. |});
  check "late quotation" ~expect:"plugin test.quot declares quotations: it must be loaded before Setup.init"
    (run ~packages:with_load "quot" {| accumulate "+test.quot". main. |});
  check "HOAS hooks" ~expect:"plugin test.hoas sets HOAS hooks: it must be loaded before Setup.init"
    (run ~packages:with_load "hoas" {| accumulate "+test.hoas". main. |});
  check "stub with builtin_stubs" ~expect:"stub ok"
    (run ~packages:dir_only ~stubs:true "stub" {| accumulate "+test.stub". main :- print "stub ok". |});
  check "stub without builtin_stubs" ~expect:"stub.f is declared builtin but no MLCode implements it"
    (run ~packages:dir_only "stub2" {| accumulate "+test.stub". main. |});
  check "separate compilation" ~expect:"+test.static " (sepcomp ());
  check "separate compilation runs" ~expect:"sepcomp 42" (sepcomp ());
  if !failures > 0 then exit 1;
  print_endline "all plugin cases ok"
