(* two projects with the same name (e.g. two worktrees): "+/x" is relative to
   the elpi.toml above the file, whatever was read before; "+same/x" is the
   project declared last *)
let () =
  let a = Elpi.API.Utils.filename_concat (Sys.getcwd ()) "same/a" and b = Elpi.API.Utils.filename_concat (Sys.getcwd ()) "same/b" in
  let p = Elpi_dynload.packages_stubs in
  let root_of dir = p.Elpi.API.Setup.root_of_dir ~dir in
  let r1 = root_of a and r2 = root_of b and r3 = root_of a in
  let declared d =
    Option.iter Elpi_dynload.declare_project (Elpi_dynload.config_above ~file:(Elpi.API.Utils.filename_concat d "x.elpi"));
    p.Elpi.API.Setup.dir ~pkg:"same" in
  let d1 = declared a and d2 = declared b in
  if String.equal r1 a && String.equal r2 b && String.equal r3 a && String.equal d1 a && String.equal d2 b
  then print_endline "same name ok"
  else Printf.printf "KO: %s %s %s %s %s\n" r1 r2 r3 d1 d2

(* the search of elpi.toml stops at the root of a repository, and does not
   look in the home directory or above *)
let () =
  let tmp = Elpi.API.Utils.filename_concat (Filename.get_temp_dir_name ()) (Printf.sprintf "elpi-toml-%d" (Unix.getpid ())) in
  let mkdir d = if not (Sys.file_exists d) then Unix.mkdir d 0o755 in
  let touch f text = let oc = open_out f in output_string oc text; close_out oc in
  let ( / ) = Elpi.API.Utils.filename_concat in
  List.iter mkdir [ tmp; tmp / "outer"; tmp / "outer" / "repo"; tmp / "outer" / "repo" / ".git";
                    tmp / "outer" / "repo" / "sub"; tmp / "home"; tmp / "home" / "sub" ];
  touch (tmp / "outer" / "elpi.toml") "name = \"outer\"\n";
  touch (tmp / "home" / "elpi.toml") "name = \"stray\"\n";
  let found f = Option.is_some (Elpi_dynload.config_above ~file:f) in
  let in_repo = found (tmp / "outer" / "repo" / "sub" / "x.elpi") in
  Unix.putenv "HOME" (tmp / "home");
  let under_home = found (tmp / "home" / "sub" / "x.elpi") in
  (* the files that also mark the root of a repository *)
  let stops marker =
    let r = tmp / "outer" / ("repo" ^ marker) in
    List.iter mkdir [ r; r / "sub" ];
    if String.equal marker ".hg" then mkdir (r / marker) else touch (r / marker) "";
    not (found (r / "sub" / "x.elpi")) in
  let markers = List.map (fun m -> m, stops m) ["dune-workspace"; "_RocqProject"; "_CoqProject"; ".hg"] in
  let expected = List.map (fun (m, _) -> m, true) markers in
  if not in_repo && not under_home && List.for_all2 (fun (_, a) (_, b) -> Bool.equal a b) markers expected
  then print_endline "search bounds ok"
  else Printf.printf "KO: in repo %b, under home %b, stops at %s\n" in_repo under_home
    (String.concat " " (List.map (fun (m, b) -> Printf.sprintf "%s=%b" m b) markers))

(* the subset of TOML: escapes, literal strings, one key per line; a renamed
   project loses its old name *)
let () =
  let tmp = Elpi.API.Utils.filename_concat (Filename.get_temp_dir_name ()) (Printf.sprintf "elpi-toml2-%d" (Unix.getpid ())) in
  if not (Sys.file_exists tmp) then Unix.mkdir tmp 0o755;
  let f = Elpi.API.Utils.filename_concat tmp "elpi.toml" in
  let write text = let oc = open_out f in output_string oc text; close_out oc in
  let wait_mtime () = Unix.sleepf 1.1 in
  write "name = \"a\\tb\\u00e9\"\nprelude = ['/C:\\dir\\x', \"/q\\\"\"]\n";
  let c = Elpi_dynload.config_of_file ~file:f in
  let ok1 = String.equal c.Elpi_dynload.name "a\tb\xc3\xa9"
    && List.equal String.equal c.Elpi_dynload.prelude ["/C:\\dir\\x"; "/q\""] in
  wait_mtime ();
  write "name = \"x\" paths = [\"y\"]\n";
  let ok2 = try ignore (Elpi_dynload.config_of_file ~file:f); false
    with Elpi.API.Error.ElpiError { loc = Some { line = 1; _ }; message = "one key per line"; component = "elpi.toml" } -> true in
  wait_mtime ();
  write "name = \"old\"\n";
  Elpi_dynload.declare_project (Elpi_dynload.config_of_file ~file:f);
  wait_mtime ();
  write "name = \"new\"\n";
  Elpi_dynload.declare_project (Elpi_dynload.config_of_file ~file:f);
  let ok3 = String.equal (Elpi_dynload.packages_stubs.Elpi.API.Setup.dir ~pkg:"new") tmp
    && (try ignore (Elpi_dynload.packages_stubs.Elpi.API.Setup.dir ~pkg:"old"); false with Elpi.API.Error.ElpiError _ -> true) in
  (* the section [warnings]: the levels in order, all is all the kinds *)
  wait_mtime ();
  write "name = \"w\"\n[warnings]\nall = \"off\"\nlinear-variable = \"error\"\n";
  let ok4 =
    let open Elpi.API.Error in
    let ws = (Elpi_dynload.config_of_file ~file:f).Elpi_dynload.warnings in
    warning_level ws LinearVariable == As_error && warning_level ws UndeclaredGlobal == Off in
  (* the section [paths]: quoted keys, a directory or a list, in order;
     the old list paths = [...] is an error *)
  wait_mtime ();
  write "name = \"p\"\n[paths]\n\"\" = \"+/lib\"\n\"a.b\" = [\"+/x\", \"+/y\"]\n";
  let ok5 =
    let ps = (Elpi_dynload.config_of_file ~file:f).Elpi_dynload.paths in
    List.equal (fun (p1, d1) (p2, d2) -> String.equal p1 p2 && String.equal d1 d2) ps
      [ "", Elpi.API.Utils.filename_concat tmp "lib"; "a.b", Elpi.API.Utils.filename_concat tmp "x"; "a.b", Elpi.API.Utils.filename_concat tmp "y" ] in
  wait_mtime ();
  write "name = \"p\"\npaths = [\"lib\"]\n";
  let ok6 = try ignore (Elpi_dynload.config_of_file ~file:f); false
    with Elpi.API.Error.ElpiError { message; _ } -> String.length message > 5 && String.equal (String.sub message 0 5) "paths" in
  (* the section [dev-only-paths]: apart from [paths]; not a list *)
  wait_mtime ();
  write "name = \"p\"\n[paths]\n\"a\" = \"+/x\"\n[dev-only-paths]\n\"t\" = [\"+/tests\"]\n";
  let ok7 =
    let c = Elpi_dynload.config_of_file ~file:f in
    let same = List.equal (fun (p1, d1) (p2, d2) -> String.equal p1 p2 && String.equal d1 d2) in
    same c.Elpi_dynload.paths [ "a", Elpi.API.Utils.filename_concat tmp "x" ]
    && same c.Elpi_dynload.dev_only_paths [ "t", Elpi.API.Utils.filename_concat tmp "tests" ] in
  wait_mtime ();
  write "name = \"p\"\ndev-only-paths = [\"+/t\"]\n";
  let ok8 = try ignore (Elpi_dynload.config_of_file ~file:f); false
    with Elpi.API.Error.ElpiError { message; _ } ->
      String.length message > 14 && String.equal (String.sub message 0 14) "dev-only-paths" in
  if ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 then print_endline "toml ok"
  else Printf.printf "KO: escapes %b, one key per line %b, rename %b, warnings %b, paths %b, old paths %b, dev-only-paths %b %b\n" ok1 ok2 ok3 ok4 ok5 ok6 ok7 ok8
