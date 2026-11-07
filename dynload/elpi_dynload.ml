(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API

(* --- the packages of findlib -------------------------------------------- *)

(* the Elpi package foo is the findlib package elpi-foo *)
let findlib_name pkg = "elpi-" ^ pkg

let init = lazy (Findlib.init ())

let no_package p msg =
  failwith (if String.equal msg "" then "no findlib package " ^ p else Printf.sprintf "no findlib package %s: %s" p msg)

(* the roots of the projects whose elpi.toml was read: their files are read
   there, not in an installed copy *)
let roots : (string, string) Hashtbl.t = Hashtbl.create 3

let dir pkg =
  match Hashtbl.find_opt roots pkg with
  | Some root -> root
  | None ->
      Lazy.force init;
      try Findlib.package_directory (findlib_name pkg)
      with Fl_package_base.No_such_package (p, msg) -> no_package p msg

let load pkg =
  Lazy.force init;
  try Fl_dynload.load_packages [findlib_name pkg] with
  | Fl_package_base.No_such_package (p, msg) -> no_package p msg
  | Dynlink.Error e -> failwith (Dynlink.error_message e)

let preload pkg = Plugin.ensure_registered ~load pkg

(* --- elpi.toml ----------------------------------------------------------- *)

(* The configuration of a project: a subset of TOML, keys whose value is a
   string or a list of strings, and # comments:
     name = "foo"                     # the package of the project
     paths = ["lib"]                  # searched by accumulate, like -I
     prelude = ["+json/utils"]        # accumulated before the main file
     preload = ["pkg"]                # plugins loaded before Setup.init *)
type config = {
  file : string;
  name : string option;
  paths : string list; (* absolute *)
  prelude : string list;
  preload : string list;
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

(* one key per line: [last] is the line where the previous entry ends *)
let parse text =
  let rec entries ~last acc = function
    | [] -> List.rev acc
    | (line, _) :: _ when line = last -> raise (Syntax (line, "one key per line"))
    | (line, key) :: (_, "=") :: (vline, v) :: rest when not (is_string key) && is_string v ->
        if List.exists (fun (k, _, _) -> String.equal k key) acc then raise (Syntax (line, "duplicate key " ^ key));
        entries ~last:vline ((key, line, String (string v)) :: acc) rest
    | (line, key) :: (_, "=") :: (_, "[") :: rest when not (is_string key) ->
        let rec values vs = function
          | (l, "]") :: rest -> List.rev vs, l, rest
          | (_, v) :: (_, ",") :: rest when is_string v -> values (string v :: vs) rest
          | (_, v) :: ((_, "]") :: _ as rest) when is_string v -> values (string v :: vs) rest
          | (l, _) :: _ -> raise (Syntax (l, "a list of strings expected"))
          | [] -> raise (Syntax (line, "] expected")) in
        let vs, l, rest = values [] rest in
        if List.exists (fun (k, _, _) -> String.equal k key) acc then raise (Syntax (line, "duplicate key " ^ key));
        entries ~last:l ((key, line, List vs) :: acc) rest
    | (line, _) :: _ -> raise (Syntax (line, "key = \"...\" or key = [ \"...\", ... ] expected")) in
  entries ~last:0 [] (tokens text)

(* the configurations read so far, by file, with the time of the file then:
   an edited file is read again *)
let configs : (string, float * config) Hashtbl.t = Hashtbl.create 3

let absolute p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p

(* the project named in [c] is found at its root (next to [c.file]), not in
   findlib: the last one declared wins *)
let declare_project c =
  let root = Filename.dirname c.file in
  (* a project renamed since it was declared: its old name is dropped *)
  let old = Hashtbl.fold (fun n r acc -> if String.equal r root then n :: acc else acc) roots [] in
  List.iter (Hashtbl.remove roots) old;
  Option.iter (fun n -> Hashtbl.replace roots n root) c.name

let config_of_file file =
  let file = absolute file in
  let mtime = try (Unix.stat file).Unix.st_mtime with Unix.Unix_error _ -> 0. in
  match Hashtbl.find_opt configs file with
  | Some (t, c) when Float.equal t mtime -> c
  | _ ->
  let text = try Parse.std_reader file with Failure msg -> failwith msg in
  let fail line msg = failwith (Printf.sprintf "%s:%d: %s" file line msg) in
  let entries = try parse text with Syntax (line, msg) -> fail line msg in
  let lists = ["paths"; "prelude"; "preload"] in
  entries |> List.iter (fun (k, line, v) ->
    match v with
    | String _ when String.equal k "name" -> ()
    | List _ when List.exists (String.equal k) lists -> ()
    | String _ when List.exists (String.equal k) lists -> fail line (k ^ " is a list of strings")
    | List _ when String.equal k "name" -> fail line "name is a string"
    | _ -> fail line ("unknown key " ^ k ^ " (name, paths, prelude and preload are)"));
  let find k = List.find_map (fun (k', _, v) -> if String.equal k k' then Some v else None) entries in
  let get k = match find k with Some (List l) -> l | _ -> [] in
  let name = match find "name" with Some (String n) -> Some n | _ -> None in
  (match name, List.find_opt (fun (k, _, _) -> String.equal k "name") entries with
   | Some n, Some (_, line, _) when String.equal n "" || String.contains n '/' || String.contains n '\\' ->
       fail line "name is a package name: not empty, no / nor \\"
   | _ -> ());
  let root = Filename.dirname file in
  let absolute p = if Filename.is_relative p then Filename.concat root p else p in
  let c = { file; name; paths = List.map absolute (get "paths"); prelude = get "prelude"; preload = get "preload" } in
  Hashtbl.replace configs file (mtime, c);
  c

(* The nearest elpi.toml in [dir] or above, up to the root of a repository
   (a directory with .git, .hg, _darcs or .jj) and not in the home directory
   or above: a stray ~/elpi.toml is not the project of every file below *)
let is_repository_root dir =
  List.exists (fun d -> Sys.file_exists (Filename.concat dir d)) [".git"; ".hg"; "_darcs"; ".jj"]

let rec config_in dir =
  let dir_slash = Filename.concat dir "" in
  let is_home_or_above =
    match Option.map (fun h -> Filename.concat h "") (Sys.getenv_opt "HOME") with
    | Some h -> String.length dir_slash <= String.length h && String.equal dir_slash (String.sub h 0 (String.length dir_slash))
    | None -> false in
  if is_home_or_above then None else
  let f = Filename.concat dir "elpi.toml" in
  if Sys.file_exists f then Some (config_of_file f)
  else if is_repository_root dir then None
  else
    let up = Filename.dirname dir in
    if String.equal up dir then None else config_in up

let config_above file = config_in (Filename.dirname (absolute file))

let root_of_dir dir =
  let dir = absolute dir in
  match config_in dir with
  | Some { file; _ } -> Filename.dirname file
  | None -> failwith (Printf.sprintf "no elpi.toml in %s or above it (up to the root of its repository)" dir)

let packages = { Setup.dir; load = Some load; root_of_dir }
let directories = { Setup.dir; load = None; root_of_dir }

(* the text that accumulates the prelude of [config] and then [file]: parsed
   with locations in the directory of elpi.toml, the prelude is relative to
   it *)
let with_prelude config file =
  let file = absolute file in
  let main =
    if Filename.check_suffix file ".elpi" then Utils.accumulate_text [Filename.chop_suffix file ".elpi"]
    else if Filename.check_suffix file ".mod" then (* Teyjus: with its .sig *)
      "import " ^ Utils.string_literal (Filename.chop_suffix file ".mod") ^ ".\n"
    else failwith (Printf.sprintf "%s: with the prelude of %s, the file must end in .elpi or .mod" file config.file) in
  Utils.accumulate_text config.prelude ^ main
