(* elpi-lsp: a language server for Elpi, speaking LSP on stdin/stdout (the
   server itself is in server/server.ml).

   As in vsrocq, the main loop is driven by Sel: the todo set holds the
   (recurrent) event reading an LSP message on stdin, and the checks of the
   documents (see Server.get_checker_tasks), which start when the user is
   idle. Reading stdin has a higher priority than checking, so a message that
   comes while the checks are queued is handled first. *)

let log = Checker.log

(* Elpi may print on stdout: the LSP messages go to a copy of the original
   stdout, and stdout itself is redirected to stderr. *)
let out = Unix.dup Unix.stdout
let () = Unix.dup2 Unix.stderr Unix.stdout

let output_json json =
  let msg = Yojson.Safe.to_string json in
  let s = Printf.sprintf "Content-Length: %d\r\n\r\n%s" (String.length msg) msg in
  let rec write off =
    if off < String.length s then
      write (off + Unix.write_substring out s off (String.length s - off)) in
  write 0

(* the files of the standard library are written on the disk *)
let builtin_library_location instance name =
  Option.map (fun (path, text) -> Lsp.Types.DocumentUri.of_path path, text) (Library_disk.file instance name)

let () = Checker.is_library_path := Library_disk.is_library_path

type event =
  | LspEvent of Yojson.Safe.t option (* a message from the client *)
  | CheckDocumentRequest of Server.checker_task  (* a check to run *)

let read_lsp_message : event Sel.Event.t =
  Sel.On.httpcle ~priority:0 ~name:"lsp" Unix.stdin (function
    | Ok buf ->
        (try LspEvent (Some (Yojson.Safe.from_string (Bytes.to_string buf)))
         with e -> log "cannot decode message: %s" (Printexc.to_string e); LspEvent None)
    | Error e -> log "cannot read stdin (%s), exiting" (Printexc.to_string e); exit 1)

let check_document task =
  Sel.now ~priority:10 ~name:"check" (CheckDocumentRequest task)

(* An opened or changed document is checked only after [idle_delay] seconds
   in which no message came from the client: the checker tasks
   (Server.get_checker_tasks) are kept in [pending], and while there are some
   the main loop waits for a message for at most [idle_delay] seconds; when
   none comes they become check events. *)
let idle_delay = 0.5

(* an exception that escapes the server (a bug) is logged, the server goes on *)
let protect what f x =
  try f x with e -> log "%s: unexpected exception %s" what (Printexc.to_string e)

let handle_event = function
  | LspEvent None -> [ read_lsp_message ]
  | LspEvent (Some json) -> protect "message" Server.handle_json json; [ read_lsp_message ]
  | CheckDocumentRequest task -> protect "check" Server.check_now task; []

let usage = {|Usage: elpi-lsp [OPTION]...
The language server of Elpi: it speaks the Language Server Protocol on its
standard input and output, for an editor. Options:
  -I DIR            a directory where accumulate looks for files, after the
                    directory of the accumulating file (more than once is ok)
  --max-errors N    the maximum number of errors reported for a file
                    (default 100)
  -debug FILE       no protocol: check FILE as when an editor opens it, print
                    its project (its elpi.toml as the server reads it) and its
                    diagnostics, and exit (1 if one is an error)
  -h, -help, --help this text
Other arguments, such as --stdio, are ignored.
|}

(* the command line: --max-errors N, the maximum number of errors per file;
   -I DIR, a directory where accumulated files are searched (as for elpi, a
   relative one is relative to the current directory); -debug FILE, check
   FILE as an editor that opens it would, print what the server finds and
   exit (see debug below); --help; the other arguments (e.g. --stdio) are
   ignored *)
let max_errors, include_paths, debug_file =
  let rec args max_errors paths debug = function
    | ("-h" | "-help" | "--help") :: _ ->
        (* on the original stdout: stdout itself is stderr, see out *)
        let s = usage in
        ignore (Unix.write_substring out s 0 (String.length s));
        exit 0
    | "--max-errors" :: n :: rest ->
        (match int_of_string_opt n with
         | Some n when n > 0 -> args (Some n) paths debug rest
         | _ -> log "invalid argument of --max-errors: %s" n; args max_errors paths debug rest)
    | "-I" :: dir :: rest -> args max_errors (dir :: paths) debug rest
    | "-debug" :: file :: rest -> args max_errors paths (Some file) rest
    | _ :: rest -> args max_errors paths debug rest
    | [] -> max_errors, List.rev paths, debug in
  args None [] None (List.tl (Array.to_list Sys.argv))

(* an error shown at the start of a document: on one line, file:line: *)
let one_line { Elpi.API.Error.loc; message; _ } =
  match loc with
  | Some { source_name; line; _ } -> Printf.sprintf "%s:%d: %s" source_name line message
  | None -> message

(* the nearest elpi.toml above a document, as for elpi; it names the project
   of the document, found in its sources ("+name/..."). Its preload plugins
   are loaded now, before the instance of the document is created, so that
   their quotations and state components are seen. A document with no path
   on the disk (e.g. untitled:) has no project. *)
let find_project_file ~path =
  if Filename.is_relative path then Server.no_project else
  (* an entry of elpi.toml that is wrong (e.g. a package of use that is not
     installed) is left out, and shown: the others count *)
  match Elpi_dynload.config_above ~recover:true ~file:path () with
  | None -> Server.no_project
  | Some ({ Elpi_dynload.file; paths; dev_only_paths; preload; warnings; errors; _ } as c) ->
      Elpi_dynload.declare_project c;
      (* the project of the document is its own: its [dev-only-paths] count *)
      let paths = paths @ dev_only_paths in
      let errors = ref (List.rev_map one_line errors) in
      let on_error e = errors := one_line e :: !errors in
      List.iter (fun pkg -> try Elpi_dynload.preload ~pkg with Elpi.API.Error.ElpiError e -> on_error e) preload;
      let builtins = Elpi_dynload.prelude_builtins ~on_error c in
      { Server.root = Filename.dirname file; paths; builtins; warnings; errors = List.rev !errors }
  | exception Elpi.API.Error.ElpiError e -> { Server.no_project with errors = [ one_line e ] }

(* --- elpi-lsp -debug FILE ------------------------------------------------- *)

(* The server checks FILE as when an editor opens it (initialize, then
   didOpen with the text of the file), with no client: what it finds is
   printed on the standard output, its log stays on the standard error. First
   the project of FILE (its elpi.toml, as the server reads it: the entries
   left out and why, the paths, the plugins preloaded, the prelude), then the
   diagnostics it publishes, as file:line:column. The exit code is 1 if one
   of them is an error. *)
let debug file =
  let oc = Unix.out_channel_of_descr out in
  let pr fmt = Printf.fprintf oc (fmt ^^ "\n%!") in
  let path = if Filename.is_relative file then Elpi.API.Utils.filename_concat (Sys.getcwd ()) file else file in
  let text = try Elpi.API.Parse.std_reader path with Failure msg -> pr "cannot read %s: %s" file msg; exit 2 in
  (* the project *)
  (match Elpi_dynload.config_above ~recover:true ~file:path () with
   | None -> pr "project: none (no elpi.toml above %s)" file
   | Some c ->
       pr "project: %s (%s)" c.Elpi_dynload.name c.Elpi_dynload.file;
       if List.length c.use > 0 then pr "  use: %s" (String.concat " " c.use);
       List.iter (fun (p, d) -> pr "  path: %s = %s%s" p d (if Sys.file_exists d then "" else " (missing)"))
         (c.paths @ c.dev_only_paths);
       List.iter (fun pkg ->
           match Elpi_dynload.preload ~pkg with
           | () -> pr "  preload: %s" pkg
           | exception Elpi.API.Error.ElpiError e -> pr "  preload: %s FAILED: %s" pkg (one_line e))
         c.preload;
       List.iter (fun e ->
           let plugin = String.length e > 1 && e.[0] = '+' && not (String.contains e '/') in
           let pkg = String.sub e 1 (max 0 (String.length e - 1)) in
           if plugin && Elpi.API.Plugin.is_registered pkg then pr "  prelude: %s (the plugin)" e
           else if plugin then pr "  prelude: %s (its stub, the plugin is not loaded)" e
           else pr "  prelude: %s" e)
         c.prelude;
       List.iter (fun (id, level) ->
           pr "  warning: %s = %s" (Elpi.API.Error.warning_name id)
             (match level with Elpi.API.Error.Off -> "off" | On -> "on" | As_error -> "error"))
         c.warnings;
       List.iter (fun e -> pr "  error (entry left out): %s" (one_line e)) c.errors
   | exception Elpi.API.Error.ElpiError e -> pr "project: error: %s" (one_line e));
  (* the diagnostics published, of FILE and of the files it accumulates *)
  let errors = ref 0 in
  let send json =
    let open Yojson.Safe.Util in
    match member "method" json with
    | `String "textDocument/publishDiagnostics" ->
        let params = member "params" json in
        let uri = to_string (member "uri" params) in
        let shown = match Lsp.Types.DocumentUri.(to_path (of_string uri)) with p -> p | exception _ -> uri in
        let ds = to_list (member "diagnostics" params) in
        pr "diagnostics of %s: %d" shown (List.length ds);
        List.iter (fun d ->
            let pos k = let p = member k (member "range" d) in
              to_int (member "line" p) + 1, to_int (member "character" p) + 1 in
            let (l1, c1), (l2, c2) = pos "start", pos "end" in
            let severity = match member "severity" d with
              | `Int 1 -> incr errors; "error" | `Int 2 -> "warning" | `Int 3 -> "info" | _ -> "hint" in
            pr "%s:%d:%d-%d:%d: %s: %s" shown l1 c1 l2 c2 severity (to_string (member "message" d)))
          ds
    | `String m -> log "debug: the server sends %s" m
    | _ -> () in
  Server.init ~send ~exit ~builtin_library_location ?max_errors ~include_paths
    ~packages:Elpi_dynload.packages_stubs ~find_project_file ();
  let notify ?id meth params =
    Server.handle_json (`Assoc ([ "jsonrpc", `String "2.0"; "method", `String meth; "params", params ]
      @ match id with Some i -> [ "id", `Int i ] | None -> [])) in
  notify ~id:1 "initialize" (`Assoc [ "processId", `Null; "rootUri", `Null; "capabilities", `Assoc [] ]);
  notify "initialized" (`Assoc []);
  notify "textDocument/didOpen" (`Assoc [ "textDocument", `Assoc [
    "uri", `String (Lsp.Types.DocumentUri.to_string (Lsp.Types.DocumentUri.of_path path));
    "languageId", `String "elpi"; "version", `Int 1; "text", `String text ] ]);
  (* the checks, now: there is no user to wait for *)
  let rec run () = match Server.get_checker_tasks () with
    | [] -> ()
    | tasks -> List.iter Server.check_now tasks; run () in
  run ();
  exit (if !errors > 0 then 1 else 0)

let () = Option.iter debug debug_file

let () =
  (* the other plugins, of accumulate "+pkg", are not loaded: their stubs are
     read *)
  Server.init ~send:output_json ~exit ~builtin_library_location ?max_errors ~include_paths
    ~packages:Elpi_dynload.packages_stubs ~find_project_file ()

let () =
  log "started";
  let rec loop todo pending =
    let pending = pending @ Server.get_checker_tasks () in
    if pending = [] then
      let ready, todo = Sel.pop todo in
      loop (Sel.Todo.add todo (handle_event ready)) []
    else
      match Sel.pop_timeout ~stop_after_being_idle_for:idle_delay todo with
      | None, todo -> loop (Sel.Todo.add todo (List.map check_document pending)) [] (* the user is idle *)
      | Some ready, todo -> loop (Sel.Todo.add todo (handle_event ready)) pending in
  loop (Sel.Todo.add Sel.Todo.empty [ read_lsp_message ]) []
