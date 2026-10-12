(* elpi-lsp for the web (e.g. vscode.dev): the server (lsp/server/server.ml)
   compiled to JavaScript or to WebAssembly, run in a web worker (see
   server-entry.js). The messages are JavaScript objects,
   received by onmessage and sent by postMessage, as vscode-languageclient's
   BrowserMessageReader and BrowserMessageWriter do.

   There is no file system: accumulate fails, and the files of the standard
   library are given to the client as elpi-builtin:/ID/NAME URIs (ID is the
   instance of Elpi of the document, see Server.library_uri), whose text is
   served by the request elpi/builtinFile. *)

open Js_of_ocaml

let global = Js.Unsafe.global

let call f args = Js.Unsafe.fun_call (Js.Unsafe.get global f) args

let post json =
  (* JSON.parse and JSON.stringify: Json.unsafe_input and Json.output are not
     implemented in the WebAssembly backend *)
  let parse = Js.Unsafe.get (Js.Unsafe.get global "JSON") "parse" in
  let v = Js.Unsafe.fun_call parse [| Js.Unsafe.inject (Js.string (Yojson.Safe.to_string json)) |] in
  ignore (call "postMessage" [| Js.Unsafe.inject v |])

let set_timeout ms f : Js.Unsafe.any =
  call "setTimeout" [| Js.Unsafe.inject (Js.wrap_callback f); Js.Unsafe.inject ms |]

let clear_timeout t = ignore (call "clearTimeout" [| Js.Unsafe.inject t |])

let library_scheme = "elpi-builtin:/"

let () =
  Server.init ~send:post ~exit:(fun _ -> ignore (call "close" [||]))
    ~builtin_library_location:(fun instance name ->
      Option.map (fun text -> Lsp.Types.DocumentUri.of_string (Server.library_uri ~prefix:library_scheme instance name), text)
        (Checker.library_text instance name))
    ();
  Checker.is_library_path := (fun path ->
    String.length path >= String.length library_scheme
    && String.equal (String.sub path 0 (String.length library_scheme)) library_scheme)

(* A change is checked only after [idle_delay] milliseconds in which no
   message came from the client: each message restarts the timer, which then
   runs the checker tasks (see Server.get_checker_tasks). *)
let idle_delay = 500

(* the checker tasks (Server.get_checker_tasks), waiting for the user to be
   idle *)
let pending = ref []
let idle_timer = ref None

let take_dirty () =
  pending := !pending @ Server.get_checker_tasks ()

let rec start_idle_timer () =
  idle_timer := Some (set_timeout idle_delay (fun () ->
    idle_timer := None;
    let tasks = !pending in
    pending := [];
    List.iter check tasks))

(* a check postponed because the user is typing waits for the next idle time *)
and check task =
  Server.check_now task;
  take_dirty ();
  if !pending <> [] && Option.is_none !idle_timer then start_idle_timer ()

let on_message event =
  Option.iter clear_timeout !idle_timer;
  idle_timer := None;
  let data = Js.Unsafe.get event "data" in
  let stringify = Js.Unsafe.get (Js.Unsafe.get global "JSON") "stringify" in
  Server.handle_json (Yojson.Safe.from_string (Js.to_string (Js.Unsafe.fun_call stringify [| Js.Unsafe.inject data |])));
  take_dirty ();
  if !pending <> [] then start_idle_timer ()

let () =
  Js.Unsafe.set global "onmessage" (Js.wrap_callback (fun event ->
    try on_message event with e -> Checker.log "cannot handle a message: %s" (Printexc.to_string e)));
  Checker.log "started (web)"
