(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API

(* --- the packages of findlib -------------------------------------------- *)

(* the package pkg of "+pkg" is the findlib package pkg, named as findlib
   does (e.g. elpi-json, rocq-elpi, or elpi-test-dyn.state for a
   subpackage) *)

(* Findlib is not initialized here: it reads its configuration and OCAMLPATH
   when the program starts, and a host may initialize it with its own settings
   (Rocq adds its directories to the search path) that Findlib.init () would
   drop *)

(* the errors about finding and loading packages, and the ones of elpi.toml *)
let packages_error msg = Error.error ~component:"Packages" msg
let config_error ?loc msg = Error.error ~component:"elpi.toml" ?loc msg

let no_package p msg =
  packages_error (if String.equal msg "" then "no findlib package " ^ p else Printf.sprintf "no findlib package %s: %s" p msg)

(* the root of each project declared with declare_project, by name: its files
   are read there, not in an installed copy *)
let projects_root : (string, string) Hashtbl.t = Hashtbl.create 3

let dir ~pkg =
  match Hashtbl.find_opt projects_root pkg with
  | Some root -> root
  | None ->
      try Findlib.package_directory pkg
      with Fl_package_base.No_such_package (p, msg) -> no_package p msg

(* "x/y/z" is ("x", "y/z"), "x" is ("x", "") *)
let split_package s =
  match String.index_opt s '/' with
  | Some i -> String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1)
  | None -> s, ""

let load ~pkg =
  try Fl_dynload.load_packages [pkg] with
  | Fl_package_base.No_such_package (p, msg) -> no_package p msg
  | Dynlink.Error e -> packages_error (Dynlink.error_message e)

let preload ~pkg = Plugin.ensure_registered ~load pkg

(* --- elpi.toml ----------------------------------------------------------- *)

(* The configuration of a project: a subset of TOML, keys whose value is a
   string or a list of strings, sections, quoted keys, and # comments:
     name = "foo"                     # the findlib package of the project (required)
     use = ["+bar"]                   # packages whose elpi.toml is used too
     prelude = ["+elpi-json/utils"]   # builtins of Setup.init, before the files
     preload = ["pkg"]                # plugins loaded before Setup.init
     [paths]                          # where accumulate finds files
     "" = "+/lib"                     # any file, like -I
     "a.b" = "+/src/b"                # a.b/x is src/b/x
     "c" = "+pkg/dir"                 # c/x is dir/x in the directory of pkg
     [dev-only-paths]                 # paths of the project's own development,
     "t" = "+/tests"                  # not of a project that uses it
     [warnings]                       # the levels of the warnings
     linear-variable = "off"          # "off", "on" or "error"; also all
   A file or a directory is "+/x" (relative to elpi.toml), "+pkg/x" or
   absolute, so that an elpi.toml installed with its package means the
   same *)
type config = {
  file : string;
  name : string; (* the findlib name of the package *)
  use : string list; (* as written *)
  paths : (string * string) list; (* the prefix ("" for any file) and an absolute directory; then the ones of use *)
  dev_only_paths : (string * string) list; (* the same, only the ones of the file: never the ones of use *)
  prelude : string list; (* "+pkg", "+pkg/file" or absolute; after the ones of use *)
  preload : string list; (* after the ones of use *)
  warnings : (Error.warning_id * Error.warning_level) list; (* in order *)
}

type value = String of string | List of string list

exception Syntax of int * string

let tokens text =
  let n = String.length text in
  let rec aux line i acc =
    if i >= n then List.rev acc else
    match text.[i] with
    | '\n' -> aux (line + 1) (i + 1) acc
    | ' ' | '\t' | '\r' -> aux line (i + 1) acc
    | '#' -> (match String.index_from_opt text i '\n' with Some j -> aux line j acc | None -> List.rev acc)
    | ('=' | '[' | ']' | ',') as c -> aux line (i + 1) ((line, String.make 1 c) :: acc)
    | '"' ->
        (* a basic string, with the escapes of TOML *)
        let b = Buffer.create 16 in
        let unicode j len =
          if j + len > n then raise (Syntax (line, "bad unicode escape"));
          match int_of_string_opt ("0x" ^ String.sub text j len) with
          | Some u when Uchar.is_valid u -> Buffer.add_utf_8_uchar b (Uchar.of_int u); j + len
          | _ -> raise (Syntax (line, "bad unicode escape")) in
        let rec str j =
          if j >= n || text.[j] = '\n' then raise (Syntax (line, "unterminated string"))
          else match text.[j] with
            | '"' -> j + 1
            | '\\' when j + 1 < n ->
                (match text.[j + 1] with
                 | 'n' -> Buffer.add_char b '\n'; str (j + 2)
                 | 't' -> Buffer.add_char b '\t'; str (j + 2)
                 | 'r' -> Buffer.add_char b '\r'; str (j + 2)
                 | 'b' -> Buffer.add_char b '\b'; str (j + 2)
                 | 'f' -> Buffer.add_char b '\012'; str (j + 2)
                 | '"' -> Buffer.add_char b '"'; str (j + 2)
                 | '\\' -> Buffer.add_char b '\\'; str (j + 2)
                 | 'u' -> str (unicode (j + 2) 4)
                 | 'U' -> str (unicode (j + 2) 8)
                 | c -> raise (Syntax (line, Printf.sprintf "unknown escape \\%c" c)))
            | c -> Buffer.add_char b c; str (j + 1) in
        let j = str (i + 1) in
        aux line j ((line, "\"" ^ Buffer.contents b) :: acc)
    | '\'' ->
        (* a literal string: no escapes *)
        (match String.index_from_opt text (i + 1) '\'' with
         | Some j when not (String.contains (String.sub text (i + 1) (j - i - 1)) '\n') ->
             aux line (j + 1) ((line, "\"" ^ String.sub text (i + 1) (j - i - 1)) :: acc)
         | _ -> raise (Syntax (line, "unterminated string")))
    | _ ->
        let j = ref i in
        while !j < n && (match text.[!j] with 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '-' -> true | _ -> false) do incr j done;
        if !j = i then raise (Syntax (line, Printf.sprintf "unexpected character %C" text.[i]));
        aux line !j ((line, String.sub text i (!j - i)) :: acc) in
  aux 1 0 []

let is_string s = String.length s > 0 && s.[0] = '"'
let string s = String.sub s 1 (String.length s - 1)
(* a key read by parse, marked by a NUL *)
let is_key s = String.length s > 0 && s.[0] = '\000'
let key_of s = String.sub s 1 (String.length s - 1)

(* one key per line: [last] is the line where the previous entry ends; a key
   after a section header [s] is s.key *)
let parse text =
  let rec entries ~section ~last acc = function
    | [] -> List.rev acc
    | (line, _) :: _ when line = last -> raise (Syntax (line, "one key per line"))
    | (_, "[") :: (_, s) :: (l, "]") :: rest when not (is_string s) ->
        entries ~section:(s ^ ".") ~last:l acc rest
    | (line, key) :: ((_, "=") :: _ as rest) ->
        (* a quoted key is a key; the ones of a section are section.key *)
        let key = if is_string key then string key else key in
        entries_of ~section ~last acc ((line, "\000" ^ section ^ key) :: rest)
    | l -> entries_of ~section ~last acc l
  and entries_of ~section ~last acc = function
    | [] -> List.rev acc
    | (line, key) :: (_, "=") :: (vline, v) :: rest when is_key key && is_string v ->
        let key = key_of key in
        if List.exists (fun (k, _, _) -> String.equal k key) acc then raise (Syntax (line, "duplicate key " ^ key));
        entries ~section ~last:vline ((key, line, String (string v)) :: acc) rest
    | (line, key) :: (_, "=") :: (_, "[") :: rest when is_key key ->
        let key = key_of key in
        let rec values vs = function
          | (l, "]") :: rest -> List.rev vs, l, rest
          | (_, v) :: (_, ",") :: rest when is_string v -> values (string v :: vs) rest
          | (_, v) :: ((_, "]") :: _ as rest) when is_string v -> values (string v :: vs) rest
          | (l, _) :: _ -> raise (Syntax (l, "a list of strings expected"))
          | [] -> raise (Syntax (line, "] expected")) in
        let vs, l, rest = values [] rest in
        if List.exists (fun (k, _, _) -> String.equal k key) acc then raise (Syntax (line, "duplicate key " ^ key));
        entries ~section ~last:l ((key, line, List vs) :: acc) rest
    | (line, _) :: _ -> raise (Syntax (line, "key = \"...\", key = [ \"...\", ... ] or [section] expected")) in
  entries ~section:"" ~last:0 [] (tokens text)

(* the names of the kinds of warnings *)
let names_of_warnings = List.map Error.warning_name Error.all_warnings

(* the configurations read so far, by file, with the digest of each elpi.toml
   read for it (the file and the ones of use): an edited file is read again.
   Not its time: it can stay the same after an edit (a resolution of 1s, on
   macOS with OCaml 4.14) *)
let configs : (string, (string * Digest.t) list * config) Hashtbl.t = Hashtbl.create 3

let stamp file = try Digest.file file with Sys_error _ -> ""

let absolute p = if Filename.is_relative p then Utils.filename_concat (Sys.getcwd ()) p else p

(* the elpi.toml of a directory *)
let toml_in dir = Utils.filename_concat dir "elpi.toml"

(* [dir] with a trailing /, to test whether a name starts with it *)
let with_slash dir =
  let d = Utils.normalize_path dir in
  if String.length d > 0 && d.[String.length d - 1] = '/' then d else d ^ "/"

(* the project named in [c] is found at its root (next to [c.file]), not in
   findlib: the last one declared wins *)
let declare_project c =
  let root = Filename.dirname c.file in
  (* a project renamed since it was declared: its old name is dropped *)
  let old = Hashtbl.fold (fun n r acc -> if String.equal r root then n :: acc else acc) projects_root [] in
  List.iter (Hashtbl.remove projects_root) old;
  Hashtbl.replace projects_root c.name root

(* l without the elements already seen before *)
let dedup eq l = List.rev (List.fold_left (fun acc x -> if List.exists (eq x) acc then acc else x :: acc) [] l)

let keys = "name, use, prelude, preload and the sections [paths], [dev-only-paths] and [warnings]"

(* the elpi.toml [file] of package [pkg] names another package *)
let name_mismatch ~pkg ~file c =
  if String.equal c.name pkg then None
  else Some (Printf.sprintf "the name in %s is %S, not the findlib name %S" file c.name pkg)

(* [visiting]: the files whose use leads to [file], for the cycles *)
let rec config_of_file_in ~visiting file =
  match Hashtbl.find_opt configs file with
  | Some (stamps, c) when List.for_all (fun (f, d) -> String.equal (stamp f) d) stamps -> stamps, c
  | _ ->
  let text = try Parse.std_reader file with Failure msg -> config_error ~loc:(Ast.Loc.initial file) msg in
  let own_stamp = Digest.string text in
  (* the location of a line of [file] *)
  let fail line msg =
    let rec start l i = if l >= line then i else match String.index_from_opt text i '\n' with
      | Some j -> start (l + 1) (j + 1) | None -> i in
    let source_start = start 1 0 in
    let source_stop = match String.index_from_opt text source_start '\n' with Some j -> j | None -> String.length text in
    config_error ~loc:{ (Ast.Loc.initial file) with line; line_starts_at = source_start; source_start; source_stop } msg in
  let entries = try parse text with Syntax (line, msg) -> fail line msg in
  let lists = ["use"; "prelude"; "preload"] in
  (* [paths] and [dev-only-paths]: "prefix" = "dir" or ["dir", ...] *)
  let in_section p k =
    let n = String.length p in
    if String.length k >= n && String.equal (String.sub k 0 n) p then Some (String.sub k n (String.length k - n)) else None in
  let path = in_section "paths." and dev_only_path = in_section "dev-only-paths." in
  (* [warnings] name = "off" | "on" | "error", name a kind of warnings or all *)
  let warning k =
    let p = "warnings." in
    let n = String.length p in
    if String.length k > n && String.equal (String.sub k 0 n) p then Some (String.sub k n (String.length k - n)) else None in
  let warning_levels line w v =
    let ids = if String.equal w "all" then List.filter_map Error.warning_of_name names_of_warnings
      else match Error.warning_of_name w with
        | Some id -> [ id ]
        | None -> fail line (Printf.sprintf "unknown warning %s (%s and all are)" w (String.concat ", " names_of_warnings)) in
    let level = match v with
      | "off" -> Error.Off | "on" -> Error.On | "error" -> Error.As_error
      | _ -> fail line (Printf.sprintf "the level of warning %s is \"off\", \"on\" or \"error\"" w) in
    List.map (fun id -> id, level) ids in
  entries |> List.iter (fun (k, line, v) ->
    match v with
    | String _ when String.equal k "name" -> ()
    | List _ when List.exists (String.equal k) lists -> ()
    | String _ when List.exists (String.equal k) lists -> fail line (k ^ " is a list of strings")
    | List _ when String.equal k "name" -> fail line "name is a string"
    | (String _ | List _) when Option.is_some (path k) || Option.is_some (dev_only_path k) -> ()
    | _ when String.equal k "paths" || String.equal k "dev-only-paths" ->
        fail line (Printf.sprintf "%s is a section: [%s], then \"prefix\" = \"+/dir\" (\"\" = \"+/dir\" for any file)" k k)
    | String s when Option.is_some (warning k) -> ignore (warning_levels line (Option.get (warning k)) s)
    | List _ when Option.is_some (warning k) -> fail line ("the level of warning " ^ Option.get (warning k) ^ " is a string")
    | _ -> fail line ("unknown key " ^ k ^ " (" ^ keys ^ " are)"));
  let warnings = entries |> List.concat_map (fun (k, line, v) ->
    match warning k, v with Some w, String s -> warning_levels line w s | _ -> []) in
  let find k = List.find_map (fun (k', _, v) -> if String.equal k k' then Some v else None) entries in
  let line_of k = match List.find_opt (fun (k', _, _) -> String.equal k k') entries with Some (_, l, _) -> l | None -> 1 in
  let get k = match find k with Some (List l) -> l | _ -> [] in
  let name = match find "name" with
    | Some (String n) when String.equal n "" || String.contains n '/' || String.contains n '\\' ->
        fail (line_of "name") "name is a findlib package name: not empty, no / nor \\"
    | Some (String n) -> n
    | _ -> fail 1 "no key name: name = \"pkg\", the findlib name of the package of the project" in
  let root = Filename.dirname file in
  (* a file or directory: "+/x" is x in the root of the project, "+pkg/x" in
     the directory of the package pkg, as for accumulate; a relative one is
     an error, so that an installed elpi.toml means the same *)
  let place line what d =
    let rest = if String.length d > 0 then String.sub d 1 (String.length d - 1) else "" in
    let pkg, sub = split_package rest in
    if String.length d = 0 || d.[0] <> '+' then
      if Filename.is_relative d then
        fail line (Printf.sprintf "%S: write \"+/%s\" (relative to elpi.toml), \"+pkg/%s\" (in a package) or an absolute %s" d d d what)
      else d
    else if String.equal pkg "" && String.contains rest '/' then Utils.filename_concat root sub
    else if String.equal pkg "" then fail line (Printf.sprintf "%S: no package after +" d)
    else
      let base = try absolute (dir ~pkg) with Error.ElpiError { Error.message; _ } -> fail line message in
      if String.equal sub "" then base else Utils.filename_concat base sub in
  let paths_of section = entries |> List.concat_map (fun (k, line, v) ->
    match section k, v with
    | Some p, String d -> [ p, place line "directory" d ]
    | Some p, List ds -> List.map (fun d -> p, place line "directory" d) ds
    | None, _ -> []) in
  let paths = paths_of path and dev_only_paths = paths_of dev_only_path in
  (* "+pkg" and "+pkg/file" are kept (the plugin, or a file found when the
     prelude is loaded), "+/file" is made absolute *)
  let prelude = get "prelude" |> List.map (fun e ->
    if String.length e > 1 && e.[0] = '+' && e.[1] <> '/' then e
    else place (line_of "prelude") "file" e) in
  (* the elpi.toml of each package of use *)
  let use = get "use" in
  let used = use |> List.map (fun u ->
    let line = line_of "use" in
    let pkg = if String.length u > 1 && u.[0] = '+' then String.sub u 1 (String.length u - 1) else "" in
    if String.equal pkg "" || String.contains pkg '/' then
      fail line (Printf.sprintf "use %S: a package is written \"+pkg\"" u);
    let d = try dir ~pkg with Error.ElpiError { Error.message; _ } -> fail line message in
    let f = absolute (toml_in d) in
    if not (Sys.file_exists f) then fail line (Printf.sprintf "use %S: no elpi.toml in %s" u d);
    if List.exists (String.equal f) (file :: visiting) then
      fail line (Printf.sprintf "use %S: a cycle (%s uses this file)" u f);
    let (_, c) as used = config_of_file_in ~visiting:(file :: visiting) f in
    (* the elpi.toml of pkg is the one of the project pkg; its
       [dev-only-paths] are not used *)
    (match name_mismatch ~pkg ~file:f c with Some msg -> fail line (Printf.sprintf "use %S: %s" u msg) | None -> ());
    used) in
  let stamps = dedup (fun (f, _) (g, _) -> String.equal f g) ((file, own_stamp) :: List.concat_map fst used) in
  let used = List.map snd used in
  let paths = dedup (fun (p, d) (q, e) -> String.equal p q && String.equal d e) (paths @ List.concat_map (fun c -> c.paths) used) in
  let prelude = dedup String.equal (List.concat_map (fun c -> c.prelude) used @ prelude) in
  let preload = dedup String.equal (List.concat_map (fun c -> c.preload) used @ get "preload") in
  let c = { file; name; use; paths; dev_only_paths; prelude; preload; warnings } in
  Hashtbl.replace configs file (stamps, c);
  stamps, c

let config_of_file ~file = snd (config_of_file_in ~visiting:[] (absolute file))

(* The nearest elpi.toml in [dir] or above, up to the root of a repository
   (a directory with .git, .hg, dune-workspace, _RocqProject or _CoqProject) and
   not in the home directory
   or above: a stray ~/elpi.toml is not the project of every file below *)
let is_repository_root dir =
  List.exists (fun d -> Sys.file_exists (Utils.filename_concat dir d)) [".git"; ".hg"; "dune-workspace"; "_RocqProject"; "_CoqProject"]

let rec config_in dir =
  let dir_slash = with_slash dir in
  let is_home_or_above =
    match Option.map with_slash (Sys.getenv_opt "HOME") with
    | Some h -> String.length dir_slash <= String.length h && String.equal dir_slash (String.sub h 0 (String.length dir_slash))
    | None -> false in
  if is_home_or_above then None else
  let f = toml_in dir in
  if Sys.file_exists f then Some (config_of_file ~file:f)
  else if is_repository_root dir then None
  else
    let up = Filename.dirname dir in
    if String.equal up dir then None else config_in up

let config_above ~file = config_in (Filename.dirname (absolute file))

let root_of_dir ~dir =
  let dir = absolute dir in
  match config_in dir with
  | Some { file; _ } -> Filename.dirname file
  | None -> packages_error (Printf.sprintf "no elpi.toml in %s or above it (up to the root of its repository)" dir)

let packages = { Setup.dir; load = Some load; root_of_dir }
let packages_stubs = { Setup.dir; load = None; root_of_dir }

(* the declarations of the files of the preludes, by file: a file is declared
   once, again under a new name if it changed *)
let prelude_files : (string, Digest.t * Setup.builtins) Hashtbl.t = Hashtbl.create 3

let builtins_of_file file =
  let text = try Parse.std_reader file with Failure msg -> config_error msg in
  let digest = Digest.string text in
  match Hashtbl.find_opt prelude_files file with
  | Some (d, b) when Digest.equal d digest -> b
  | old ->
      let file_name = match old with None -> file | Some _ -> Printf.sprintf "%s (%s)" file (Digest.to_hex digest) in
      let b = BuiltIn.declare ~file_name [ BuiltIn.LPCode text ] in
      Hashtbl.replace prelude_files file (digest, b);
      b

(* the file of an entry of the prelude, as accumulate finds it: .elpi is
   added; "+/file" was made absolute when elpi.toml was read *)
let prelude_file config entry =
  let root = Filename.dirname config.file in
  let with_ext f = if Filename.check_suffix f ".elpi" then f else f ^ ".elpi" in
  if String.length entry > 0 && entry.[0] = '+' then
    match split_package (String.sub entry 1 (String.length entry - 1)) with
    | "", file when String.contains entry '/' -> Utils.filename_concat root (with_ext file)
    | pkg, "" when not (String.contains entry '/') -> Utils.filename_concat (dir ~pkg) (pkg ^ ".builtins.elpi")
    | pkg, file -> Utils.filename_concat (dir ~pkg) (with_ext file)
  else if Filename.is_relative entry then Utils.filename_concat root (with_ext entry)
  else with_ext entry

let prelude_builtins config =
  config.prelude |> List.map (fun entry ->
    let plugin = String.length entry > 1 && entry.[0] = '+' && not (String.contains entry '/') in
    let pkg = String.sub entry 1 (max 0 (String.length entry - 1)) in
    if plugin && Plugin.is_registered pkg then Plugin.builtins pkg
    else builtins_of_file (prelude_file config entry))

(* --- checking an installed package ---------------------------------------- *)

type check_result = Checked of string | Failed of string list
type report = (string * check_result) list

(* the .elpi files under [dir], but the stubs, relative to it and sorted;
   symlinked directories are followed, each real directory once *)
let elpi_files dir =
  let seen = Hashtbl.create 7 in
  let rec walk rel =
    let d = if String.equal rel "" then dir else Utils.filename_concat dir rel in
    let real = try Unix.realpath d with Unix.Unix_error _ -> d in
    if Hashtbl.mem seen real then [] else begin
      Hashtbl.add seen real ();
      let entries = try Sys.readdir d with Sys_error _ -> [||] in
      Array.sort String.compare entries;
      Array.to_list entries |> List.concat_map (fun e ->
        (* with /, also on Windows: r is shown as +pkg/r *)
        let r = if String.equal rel "" then e else rel ^ "/" ^ e in
        let full = Utils.filename_concat dir r in
        if Sys.is_directory full then walk r
        else if Filename.check_suffix e ".elpi" && not (Filename.check_suffix e ".builtins.elpi") then [ r ]
        else [])
    end in
  walk ""

let show_errors errors = List.map Error.show errors

let check_package ~pkg =
  let report = ref [] in
  let add item result = report := (item, result) :: !report in
  let failed_of = function
    | Error.ElpiError e -> Failed [ Error.show e ]
    | Failure msg | Sys_error msg -> Failed [ msg ]
    | e -> raise e in
  (* the installed directory, not a project declared in its sources *)
  match (try Ok (Findlib.package_directory pkg) with
         | Fl_package_base.No_such_package (p, msg) ->
             Error (if String.equal msg "" then "no findlib package " ^ p else Printf.sprintf "no findlib package %s: %s" p msg)) with
  | Error msg -> add pkg (Failed [ msg ]); List.rev !report
  | Ok dir ->
  let dir = absolute dir in
  let toml = toml_in dir in
  let empty = { file = toml; name = pkg; use = []; paths = []; dev_only_paths = []; prelude = []; preload = []; warnings = [] } in
  (* 1. its elpi.toml, read as use reads it: [dev-only-paths] are not used *)
  let config =
    if not (Sys.file_exists toml) then begin
      add "elpi.toml" (Checked (Printf.sprintf "none (only \"+%s/file\" accumulates)" pkg)); Some empty
    end else
      match snd (config_of_file_in ~visiting:[] toml) with
      | c ->
          (match name_mismatch ~pkg ~file:toml c with
           | Some msg -> add "elpi.toml" (Failed [ msg ])
           | None ->
               let uses = if List.length c.use = 0 then "" else ", uses " ^ String.concat " " c.use in
               add "elpi.toml" (Checked (Printf.sprintf "ok (name %s%s)" c.name uses)));
          Some c
      | exception e -> add "elpi.toml" (failed_of e); None in
  match config with
  | None -> List.rev !report
  | Some config ->
  (* 2. the plugin, if the package has a stub: it is an Elpi plugin *)
  let stub = Utils.filename_concat dir (pkg ^ ".builtins.elpi") in
  let plugin_ok =
    if not (Sys.file_exists stub) then None
    else match preload ~pkg with
      | () -> Some ()
      | exception e -> add ("+" ^ pkg) (failed_of e); None in
  (* 3. the instance that checks the files, as elpi-lsp checks a document
     of a project that uses the package: its preload, its prelude, its
     paths, the stubs of the plugins; a directory under [dir] has [dir] as
     its root *)
  let elpi =
    try
      List.iter (fun pkg -> preload ~pkg) config.preload;
      let prefixes = List.filter (fun (p, _) -> not (String.equal p "")) config.paths in
      let dirs = List.filter_map (fun (p, d) -> if String.equal p "" then Some d else None) config.paths in
      let under d = let d = with_slash (absolute d) and r = with_slash dir in
        String.length d >= String.length r && String.equal (String.sub d 0 (String.length r)) r in
      let packages = { packages_stubs with Setup.root_of_dir = (fun ~dir:d -> if under d then dir else root_of_dir ~dir:d) } in
      let flags = { Compile.default_flags with Compile.builtin_stubs = true; max_errors = 5 } in
      Some (flags, Setup.init ~flags:(Compile.to_setup_flags flags)
        ~builtins:(Elpi.Builtin.std_builtins :: prelude_builtins config)
        ~file_resolver:(Parse.std_resolver ~prefixes ~paths:dirs ()) ~packages ())
    with e -> add "prelude" (failed_of e); None in
  (* parsed and compiled, its errors *)
  let check flags elpi file =
    match Parse.program ~flags ~elpi file with
    | _, (_ :: _ as errors), _ -> show_errors errors
    | ast, [], _ ->
        let _, errors, _ = Compile.program ~flags ~elpi ast in
        show_errors errors
    | exception e -> (match failed_of e with Failed m -> m | Checked _ -> []) in
  (match plugin_ok, elpi with
   | Some (), Some (flags, elpi) ->
       let errors = check flags elpi stub in
       let text = try Some (Parse.std_reader stub) with Failure _ -> None in
       let doc = Format.asprintf "%a" BuiltIn.document_fmt (Plugin.builtins pkg) in
       (* a stub written on Windows (stdout in text mode) ends its lines with \r\n *)
       let without_cr s = String.concat "" (String.split_on_char '\r' s) in
       let stale = match text with
         | Some t when String.equal (without_cr t) (without_cr doc) -> []
         | _ -> [ Printf.sprintf "%s differs from the documentation of the plugin (regenerate it with BuiltIn.document_fmt)" stub ] in
       (match errors @ stale with
        | [] -> add ("+" ^ pkg) (Checked "ok (plugin loaded, stub up to date)")
        | e -> add ("+" ^ pkg) (Failed e))
   | Some (), None -> add ("+" ^ pkg) (Checked "plugin loaded (the stub is not checked)")
   | None, _ -> ());
  (* 4. the files of +pkg/...; the ones of the prelude were compiled by
     Setup.init, compiling them again would declare their contents twice *)
  let real f = try Unix.realpath f with Unix.Unix_error _ -> f in
  let prelude_files = config.prelude |> List.filter_map (fun entry ->
    let plugin = String.length entry > 1 && entry.[0] = '+' && not (String.contains entry '/') in
    if plugin then None else try Some (real (prelude_file config entry)) with Error.ElpiError _ -> None) in
  (match elpi with
   | None -> ()
   | Some (flags, elpi) ->
       elpi_files dir |> List.iter (fun rel ->
         let item = "+" ^ pkg ^ "/" ^ Filename.chop_suffix rel ".elpi" in
         let file = Utils.filename_concat dir rel in
         if List.exists (String.equal (real file)) prelude_files then add item (Checked "ok (in the prelude)")
         else match check flags elpi file with
         | [] -> add item (Checked "ok")
         | errors -> add item (Failed errors)));
  List.rev !report
