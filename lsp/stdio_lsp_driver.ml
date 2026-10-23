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

(* the command line: --max-errors N, the maximum number of errors per file;
   the other arguments (e.g. --stdio) are ignored *)
let max_errors =
  let rec args max_errors = function
    | "--max-errors" :: n :: rest ->
        (match int_of_string_opt n with
         | Some n when n > 0 -> args (Some n) rest
         | _ -> log "invalid argument of --max-errors: %s" n; args max_errors rest)
    | _ :: rest -> args max_errors rest
    | [] -> max_errors in
  args None (List.tl (Array.to_list Sys.argv))

let () =
  Server.init ~send:output_json ~exit ~builtin_library_location ?max_errors ()

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
