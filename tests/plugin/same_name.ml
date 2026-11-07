(* two projects with the same name (e.g. two worktrees): "+/x" is relative to
   the elpi.toml above the file, whatever was read before; "+same/x" is the
   project declared last *)
let () =
  let a = Filename.concat (Sys.getcwd ()) "same/a" and b = Filename.concat (Sys.getcwd ()) "same/b" in
  let p = Elpi_dynload.directories in
  let root_of d = p.Elpi.API.Setup.root_of_dir d in
  let r1 = root_of a and r2 = root_of b and r3 = root_of a in
  let declared d =
    Option.iter Elpi_dynload.declare_project (Elpi_dynload.config_above (Filename.concat d "x.elpi"));
    p.Elpi.API.Setup.dir "same" in
  let d1 = declared a and d2 = declared b in
  if String.equal r1 a && String.equal r2 b && String.equal r3 a && String.equal d1 a && String.equal d2 b
  then print_endline "same name ok"
  else Printf.printf "KO: %s %s %s %s %s\n" r1 r2 r3 d1 d2

(* the search of elpi.toml stops at the root of a repository, and does not
   look in the home directory or above *)
let () =
  let tmp = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "elpi-toml-%d" (Unix.getpid ())) in
  let mkdir d = if not (Sys.file_exists d) then Unix.mkdir d 0o755 in
  let touch f text = let oc = open_out f in output_string oc text; close_out oc in
  let ( / ) = Filename.concat in
  List.iter mkdir [ tmp; tmp / "outer"; tmp / "outer" / "repo"; tmp / "outer" / "repo" / ".git";
                    tmp / "outer" / "repo" / "sub"; tmp / "home"; tmp / "home" / "sub" ];
  touch (tmp / "outer" / "elpi.toml") "name = \"outer\"\n";
  touch (tmp / "home" / "elpi.toml") "name = \"stray\"\n";
  let found f = Option.is_some (Elpi_dynload.config_above f) in
  let in_repo = found (tmp / "outer" / "repo" / "sub" / "x.elpi") in
  Unix.putenv "HOME" (tmp / "home");
  let under_home = found (tmp / "home" / "sub" / "x.elpi") in
  if not in_repo && not under_home then print_endline "search bounds ok"
  else Printf.printf "KO: in repo %b, under home %b\n" in_repo under_home

(* the subset of TOML: escapes, literal strings, one key per line; a renamed
   project loses its old name *)
let () =
  let tmp = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "elpi-toml2-%d" (Unix.getpid ())) in
  if not (Sys.file_exists tmp) then Unix.mkdir tmp 0o755;
  let f = Filename.concat tmp "elpi.toml" in
  let write text = let oc = open_out f in output_string oc text; close_out oc in
  let wait_mtime () = Unix.sleepf 1.1 in
  write "name = \"a\\tb\\u00e9\"\nprelude = ['C:\\dir\\x', \"q\\\"\"]\n";
  let c = Elpi_dynload.config_of_file f in
  let ok1 = Option.equal String.equal c.Elpi_dynload.name (Some "a\tb\xc3\xa9")
    && List.equal String.equal c.Elpi_dynload.prelude ["C:\\dir\\x"; "q\""] in
  wait_mtime ();
  write "name = \"x\" paths = [\"y\"]\n";
  let ok2 = try ignore (Elpi_dynload.config_of_file f); false with Failure msg ->
    let rex = Str.regexp_string "elpi.toml:1: one key per line" in
    (try ignore (Str.search_forward rex msg 0); true with Not_found -> false) in
  wait_mtime ();
  write "name = \"old\"\n";
  Elpi_dynload.declare_project (Elpi_dynload.config_of_file f);
  wait_mtime ();
  write "name = \"new\"\n";
  Elpi_dynload.declare_project (Elpi_dynload.config_of_file f);
  let ok3 = String.equal (Elpi_dynload.directories.Elpi.API.Setup.dir "new") tmp
    && (try ignore (Elpi_dynload.directories.Elpi.API.Setup.dir "old"); false with Failure _ -> true) in
  if ok1 && ok2 && ok3 then print_endline "toml ok"
  else Printf.printf "KO: escapes %b, one key per line %b, rename %b\n" ok1 ok2 ok3
