(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi.API

(* --- the packages of findlib -------------------------------------------- *)

let init = lazy (Findlib.init ())

let no_package p msg =
  failwith (if String.equal msg "" then "no findlib package " ^ p else Printf.sprintf "no findlib package %s: %s" p msg)

let dir pkg =
  Lazy.force init;
  try Findlib.package_directory pkg
  with Fl_package_base.No_such_package (p, msg) -> no_package p msg

let load pkg =
  Lazy.force init;
  try Fl_dynload.load_packages [pkg] with
  | Fl_package_base.No_such_package (p, msg) -> no_package p msg
  | Dynlink.Error e -> failwith (Dynlink.error_message e)

let packages = { Setup.dir; load = Some load }
let directories = { Setup.dir; load = None }

let preload pkg =
  if not (Plugin.is_registered pkg) then begin
    load pkg;
    if not (Plugin.is_registered pkg) then
      failwith (Printf.sprintf "package %s did not register its plugin (Elpi.API.Plugin.register ~name:%S)" pkg pkg)
  end

(* --- elpi.toml ----------------------------------------------------------- *)

(* The configuration of a project: a subset of TOML, keys whose value is a
   list of strings, and # comments:
     paths = ["lib"]                  # searched by accumulate, like -I
     prelude = ["+elpi-json/utils"]   # accumulated before the main file
     preload = ["pkg"]                # plugins loaded before Setup.init *)
type config = {
  file : string;
  paths : string list; (* absolute *)
  prelude : string list;
  preload : string list;
}

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
        let b = Buffer.create 16 in
        let rec str j =
          if j >= n || text.[j] = '\n' then raise (Syntax (line, "unterminated string"))
          else match text.[j] with
            | '"' -> j + 1
            | '\\' when j + 1 < n -> Buffer.add_char b text.[j + 1]; str (j + 2)
            | c -> Buffer.add_char b c; str (j + 1) in
        let j = str (i + 1) in
        aux line j ((line, "\"" ^ Buffer.contents b) :: acc)
    | _ ->
        let j = ref i in
        while !j < n && (match text.[!j] with 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '-' -> true | _ -> false) do incr j done;
        if !j = i then raise (Syntax (line, Printf.sprintf "unexpected character %C" text.[i]));
        aux line !j ((line, String.sub text i (!j - i)) :: acc) in
  aux 1 0 []

let is_string s = String.length s > 0 && s.[0] = '"'
let string s = String.sub s 1 (String.length s - 1)

let parse text =
  let rec entries acc = function
    | [] -> List.rev acc
    | (line, key) :: (_, "=") :: (_, "[") :: rest when not (is_string key) ->
        let rec values vs = function
          | (_, "]") :: rest -> List.rev vs, rest
          | (_, v) :: (_, ",") :: rest when is_string v -> values (string v :: vs) rest
          | (_, v) :: ((_, "]") :: _ as rest) when is_string v -> values (string v :: vs) rest
          | (l, _) :: _ -> raise (Syntax (l, "a list of strings expected"))
          | [] -> raise (Syntax (line, "] expected")) in
        let vs, rest = values [] rest in
        if List.exists (fun (k, _, _) -> String.equal k key) acc then raise (Syntax (line, "duplicate key " ^ key));
        entries ((key, line, vs) :: acc) rest
    | (line, _) :: _ -> raise (Syntax (line, "key = [ \"...\", ... ] expected")) in
  entries [] (tokens text)

let config_of_file file =
  let text = try Parse.std_reader file with Failure msg -> failwith msg in
  let fail line msg = failwith (Printf.sprintf "%s:%d: %s" file line msg) in
  let entries = try parse text with Syntax (line, msg) -> fail line msg in
  entries |> List.iter (fun (k, line, _) ->
    if not (List.exists (String.equal k) ["paths"; "prelude"; "preload"]) then
      fail line ("unknown key " ^ k ^ " (paths, prelude and preload are)"));
  let get k = Option.value ~default:[] (List.find_map (fun (k', _, v) -> if String.equal k k' then Some v else None) entries) in
  let root = Filename.dirname file in
  let absolute p = if Filename.is_relative p then Filename.concat root p else p in
  { file; paths = List.map absolute (get "paths"); prelude = get "prelude"; preload = get "preload" }

(* the elpi.toml next to [file], if any *)
let config_next_to file =
  let f = Filename.concat (Filename.dirname file) "elpi.toml" in
  if Sys.file_exists f then Some (config_of_file f) else None

(* the text that accumulates the prelude of [config] and then [file]: parsed
   with locations in the directory of elpi.toml, the prelude is relative to
   it *)
let with_prelude config file =
  let acc s = Printf.sprintf "accumulate %S.\n" s in
  let file = if Filename.is_relative file then Filename.concat (Sys.getcwd ()) file else file in
  let file = Filename.remove_extension file in
  String.concat "" (List.map acc config.prelude) ^ acc file
