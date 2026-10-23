(* The language server, independent of how messages come and go: the driver
   (../stdio_lsp_driver.ml on stdin/stdout, or ../web_driver.ml in a web
   worker) calls [init], gives the messages of the client to [handle_json],
   and runs the checker tasks ([get_checker_tasks], [check_now]) when it sees
   fit. See server.mli. *)

open Lsp.Types

let log = Checker.log

(* --- given by the driver (init) ------------------------------------------------- *)

(* the functions given by the driver: set by init, used only through the
   functions below *)
let send_ref : (Yojson.Safe.t -> unit) ref = ref (fun _ -> ())
let exit_ref : (int -> unit) ref = ref Stdlib.exit
let builtin_library_location_ref : (Checker.instance -> string -> (DocumentUri.t * string) option) ref =
  ref (fun _ _ -> None)

(* whether init was called *)
let init_called = ref false

let init ~send ~exit ~builtin_library_location ?max_errors () =
  send_ref := send;
  exit_ref := exit;
  builtin_library_location_ref := builtin_library_location;
  Option.iter (fun n -> Checker.max_errors := n) max_errors;
  init_called := true

(* sends a message to the client *)
let send json = !send_ref json

(* the exit notification *)
let exit code = !exit_ref code

(* where go to definition finds a file of the standard library of an
   instance: its URI and its text *)
let builtin_library_location instance name = !builtin_library_location_ref instance name

(* --- output ------------------------------------------------------------------ *)

let send_notification n =
  send (Jsonrpc.Notification.yojson_of_t (Lsp.Server_notification.to_jsonrpc n))

(* --- documents --------------------------------------------------------------- *)

type document = {
  path : string;                    (* the name of the document for the checker *)
  mutable text : Text.t;
  mutable version : int;            (* the version of the client, it grows at each change *)
  mutable checked : int;            (* the version last checked *)
  mutable hover : Checker.hover option; (* the symbols of the last checked version *)
  instance : Checker.instance;      (* the instance of Elpi of the document *)
}

let documents : (DocumentUri.t, document) Hashtbl.t = Hashtbl.create 7

(* a file: URI is a path; other schemes (e.g. vscode-vfs: in vscode.dev, or
   untitled:) have no path, the whole URI names the document *)
let path_of_uri uri =
  let s = DocumentUri.to_string uri in
  if String.length s >= 5 && String.equal (String.sub s 0 5) "file:" then DocumentUri.to_path uri else s

(* The documents opened or changed since their last checker task was taken:
   the driver decides when to check them (see server.mli). *)
let dirty : (DocumentUri.t, unit) Hashtbl.t = Hashtbl.create 7

(* a check to run: a version of a document *)
type checker_task = DocumentUri.t * int

let check_later uri = Hashtbl.replace dirty uri ()

let has_dirty () = Hashtbl.length dirty > 0

(* the checker tasks of the dirty documents, which are no longer dirty *)
let get_checker_tasks () =
  let uris = Hashtbl.fold (fun uri () acc -> uri :: acc) dirty [] in
  Hashtbl.reset dirty;
  List.filter_map (fun uri ->
      Option.map (fun doc -> uri, doc.version) (Hashtbl.find_opt documents uri)) uris

let severity : Checker.severity -> DiagnosticSeverity.t = function
  | Error -> Error
  | Warning -> Warning
  | Information -> Information

let check uri doc =
  let t0 = Unix.gettimeofday () in
  let { Checker.diagnostics; hover } = Checker.check ~instance:doc.instance ~path:doc.path doc.text.Text.text in
  log "checked %s (version %d) in %.3fs: %d diagnostics" doc.path doc.version
    (Unix.gettimeofday () -. t0) (List.length diagnostics);
  doc.checked <- doc.version;
  doc.hover <- hover;
  let diagnostics = List.map (fun { Checker.start; stop; severity = s; message } ->
      Diagnostic.create ~range:(Text.range doc.text start stop) ~severity:(severity s)
        ~source:"elpi" ~message:(`String message) ()) diagnostics in
  send_notification (PublishDiagnostics (PublishDiagnosticsParams.create ~uri ~version:doc.version ~diagnostics ()))

(* the hover information of a document, checking it first if needed *)
let hover_of uri =
  match Hashtbl.find_opt documents uri with
  | None -> None
  | Some doc ->
      if not (Int.equal doc.checked doc.version) then check uri doc;
      Option.map (fun h -> doc, h) doc.hover

(* checks a version of a document, unless it was closed, changed since, or
   already checked; if a document changed since the task was taken, the task
   is given again by get_checker_tasks *)
let check_now ((uri, version) : checker_task) =
  match Hashtbl.find_opt documents uri with
  | Some doc when Int.equal doc.version version && not (Int.equal doc.checked version) && has_dirty () ->
      check_later uri
  | Some doc when Int.equal doc.version version && not (Int.equal doc.checked version) ->
      (try check uri doc with e ->
         (* the old diagnostics must not stay: the failure is shown *)
         log "check failed: %s" (Printexc.to_string e);
         doc.checked <- doc.version;
         send_notification (PublishDiagnostics (PublishDiagnosticsParams.create ~uri ~version:doc.version
           ~diagnostics:[ Diagnostic.create ~range:(Text.range doc.text 0 0)
                            ~severity:DiagnosticSeverity.Error ~source:"elpi"
                            ~message:(`String ("internal error of the server: " ^ Printexc.to_string e)) () ] ())))
  | _ -> ()

(* --- requests ------------------------------------------------------------------ *)

(* the options of the client: { maxErrors: N }, they override the ones of the
   driver (see init) *)
let set_client_options = function
  | Some (`Assoc l) ->
      (match List.assoc_opt "maxErrors" l with
       | Some (`Int n) when n > 0 -> Checker.max_errors := n
       | _ -> ())
  | _ -> ()

(* whether the client takes a LocationLink as the answer to a definition
   request *)
let link_support = ref false

let initialize (params : InitializeParams.t) =
  Option.iter Checker.set_trace params.trace;
  link_support :=
    (match params.capabilities.textDocument with
     | Some { definition = Some { linkSupport = Some b; _ }; _ } -> b
     | _ -> false);
  set_client_options params.initializationOptions;
  let textDocumentSync =
    `TextDocumentSyncOptions (TextDocumentSyncOptions.create ~openClose:true ~save:(`Bool true)
                                ~change:TextDocumentSyncKind.Full ()) in
  let semanticTokensProvider =
    `SemanticTokensOptions (SemanticTokensOptions.create ~full:(`Bool true)
      ~legend:(SemanticTokensLegend.create ~tokenTypes:Checker.token_types ~tokenModifiers:Checker.token_modifiers) ()) in
  let capabilities = ServerCapabilities.create ~textDocumentSync
      ~hoverProvider:(`Bool true) ~definitionProvider:(`Bool true) ~documentHighlightProvider:(`Bool true) ~semanticTokensProvider () in
  InitializeResult.create ~capabilities
    ~serverInfo:(InitializeResult.create_serverInfo ~name:"elpi-lsp" ~version:"0.1" ()) ()

(* the text of a file, to convert the location of a definition *)
let text_of_file doc file =
  if String.equal file doc.path then Some doc.text
  else if Sys.file_exists file then
    try
      let ic = open_in_bin file in
      let s = Fun.protect ~finally:(fun () -> close_in ic)
          (fun () -> really_input_string ic (in_channel_length ic)) in
      Some (Text.make s)
    with Sys_error _ -> None
  else None

(* the text and the URI of the file of a location (the [source_name] of a
   location of [doc]'s program): the document (whose path can be a whole URI,
   e.g. untitled:), a file of the library (it does not exist: its name is
   relative, and a file of the user next to the document can have the same
   name), or a file (relative to the document) *)
let source_text doc uri source_name =
  if String.equal source_name doc.path then Some (doc.text, uri)
  else if Filename.is_relative source_name && Option.is_some (Checker.library_text doc.instance source_name) then
    Option.map (fun (uri, text) -> Text.make text, uri) (builtin_library_location doc.instance source_name)
  else
    let file =
      if Filename.is_relative source_name
      then Filename.concat (Filename.dirname doc.path) source_name else source_name in
    Option.map (fun t -> t, if String.equal file doc.path then uri else DocumentUri.of_path file)
      (text_of_file doc file)

let hover ({ textDocument = { uri }; position; _ } : HoverParams.t) =
  match hover_of uri with
  | None -> None
  | Some (doc, h) ->
      let off = Text.offset_of_position doc.text position in
      match Checker.hover_at ~path:doc.path ~text:doc.text.Text.text off h with
      | None -> None
      | Some { range = { source_start; source_stop; _ }; term; type_ = ty; binder; doc = documentation } ->
          (* the range is highlighted by the client; the term is quoted *)
          (* the type is formatted on its own: after "term : ", its next lines
             are indented as much, to stay aligned with its first line *)
          let value = match term with
            | Some t ->
                let prefix = t ^ " : " in
                let ty = String.concat ("\n" ^ String.make (String.length prefix) ' ') (String.split_on_char '\n' ty) in
                Printf.sprintf "```elpi-hover\n%s%s\n```" prefix ty
            | None -> Printf.sprintf "```elpi-hover\n%s\n```" ty in
          let value = match binder with None -> value | Some b -> value ^ "\n\n" ^ b in
          (* the documentation of a constant: the comment block before its
             declaration *)
          let value =
            match Option.bind documentation (fun (d : Elpi.API.Ast.Loc.t) ->
                Option.map (fun (t, _) -> Checker.doc_text t.Text.text d) (source_text doc uri d.source_name)) with
            | Some d when not (String.equal d "") -> value ^ "\n\n---\n\n" ^ d
            | _ -> value in
          let contents = `MarkupContent (MarkupContent.create ~kind:Markdown ~value) in
          Some (Hover.create ~contents ~range:(Text.range doc.text source_start source_stop) ())

(* The range that the client previews for a definition (e.g. VS Code on
   Ctrl+hover): the declaration, extended with the body (the rules) when it
   follows the declaration (only its final dot and blank space in between),
   up to 8 lines: VS Code previews a range of at most 8 lines as it is, a
   longer one is reduced to its first line *)
let preview_lines = 8

let preview_range (t : Text.t) (defined : Elpi.API.Ast.Loc.t) (body : Elpi.API.Ast.Loc.t option) =
  let stop =
    match body with
    | Some (b : Elpi.API.Ast.Loc.t)
      when String.equal b.source_name defined.source_name && b.source_start >= defined.source_stop
           && b.source_stop <= String.length t.Text.text
           && String.for_all (function ' ' | '\t' | '\r' | '\n' | '.' -> true | _ -> false)
                (String.sub t.Text.text defined.source_stop (b.source_start - defined.source_stop)) ->
        b.source_stop
    | _ -> defined.source_stop in
  let first = (Text.position_of_offset t defined.source_start).line in
  let last = first + preview_lines - 1 in
  let stop =
    if (Text.position_of_offset t stop).line <= last then stop
    else Text.offset_of_position t { line = last; character = max_int } in
  Text.range t defined.source_start stop

let definition ({ textDocument = { uri }; position; _ } : DefinitionParams.t) : Locations.t option =
  match hover_of uri with
  | None -> None
  | Some (doc, h) ->
      let off = Text.offset_of_position doc.text position in
      match Checker.definition_at ~path:doc.path off h with
      | None -> None
      | Some (origin, ({ source_name; _ } as defined), body) ->
          (* builtins are defined in files that do not exist *)
          match source_text doc uri source_name with
          | None -> None
          | Some (t, target) ->
              let defined = Checker.complete_binder t.Text.text defined in
              let range = Text.range t defined.source_start defined.source_stop in
              if !link_support then
                (* the client jumps to the declaration, and previews it with
                   the body *)
                Some (`LocationLink [ LocationLink.create ~targetUri:target
                  ~originSelectionRange:(Text.range doc.text origin.source_start origin.source_stop)
                  ~targetSelectionRange:range ~targetRange:(preview_range t defined body) () ])
              else Some (`Location [ Location.create ~uri:target ~range ])

(* the binder of the variable under the cursor (Write), and its occurrences
   (Read) *)
let highlight ({ textDocument = { uri }; position; _ } : DocumentHighlightParams.t) =
  match hover_of uri with
  | None -> None
  | Some (doc, h) ->
      let off = Text.offset_of_position doc.text position in
      let range (l : Elpi.API.Ast.Loc.t) = Text.range doc.text l.source_start l.source_stop in
      match Checker.highlights_at ~path:doc.path off h with
      | [] -> None
      | l ->
          Some (List.filter_map (function
            | Checker.Binder_of_variable b when String.equal b.source_name doc.path ->
                let b = Checker.complete_binder doc.text.Text.text b in
                Some (DocumentHighlight.create ~kind:DocumentHighlightKind.Write ~range:(range b) ())
            | Checker.Binder_of_variable _ -> None
            | Checker.Definition_of_constant d ->
                Some (DocumentHighlight.create ~kind:DocumentHighlightKind.Write ~range:(range d) ())
            | Checker.Occurrence o -> Some (DocumentHighlight.create ~kind:DocumentHighlightKind.Read ~range:(range o) ())) l)

(* the colors of a document, from the symbols of the units *)
let semantic_tokens ({ textDocument = { uri }; _ } : SemanticTokensParams.t) =
  match hover_of uri with
  | None -> None
  | Some (doc, h) -> Some (SemanticTokens.create ~data:(Checker.semantic_tokens ~path:doc.path doc.text h) ())

(* the URI of the file [name] of the library of [instance]: [prefix]ID/NAME,
   where ID is the instance (see builtin_file) *)
let library_uri ~prefix instance name =
  Printf.sprintf "%s%d/%s" prefix (Checker.id instance) (Filename.basename name)

(* elpi/builtinFile { uri }: the text of a file of the standard library, for a
   client that shows the URIs given by [builtin_library_location], made by
   [library_uri]: the file of the library of that instance, if a document
   that has it is still open *)
let builtin_file (params : Jsonrpc.Structured.t option) : Yojson.Safe.t =
  match params with
  | Some (`Assoc l) ->
      (match List.assoc_opt "uri" l with
       | Some (`String uri) ->
           let id = int_of_string_opt (Filename.basename (Filename.dirname uri)) in
           let instance = Hashtbl.fold (fun _ (doc : document) acc ->
               match acc, id with
               | None, Some id when Int.equal (Checker.id doc.instance) id -> Some doc.instance
               | _ -> acc) documents None in
           (match Option.bind instance (fun i -> Checker.library_text i (Filename.basename uri)) with
            | Some text -> `String text
            | None -> `Null)
       | _ -> `Null)
  | _ -> `Null

(* elpi/run { textDocument: { uri }, query, text?, maxSteps? }: runs the query
   on the document, or on [text] when given (then the document needs not be
   open), for at most maxSteps steps of the interpreter (default_max_steps if
   not given: the server answers one message at a time, a query that does not
   terminate would block it); the result is the one of Runner.run. With [text], the URI can be the one of a directory (it ends
   with / or it is an existing directory): the text is then a file of that
   directory, for the locations and accumulate. *)
let default_max_steps = 1_000_000

let text_path uri =
  let p = path_of_uri uri in
  let is_dir = (try Sys.is_directory p with Sys_error _ -> false)
               || (String.length p > 0 && Char.equal p.[String.length p - 1] '/') in
  if is_dir then Filename.concat p "(text)" else p

let run (params : Jsonrpc.Structured.t option) : (Yojson.Safe.t, Jsonrpc.Response.Error.Code.t * string) result =
  let field name = match params with Some (`Assoc l) -> List.assoc_opt name l | _ -> None in
  let uri =
    match field "textDocument" with
    | Some (`Assoc l) -> (match List.assoc_opt "uri" l with Some (`String u) -> Some (DocumentUri.of_string u) | _ -> None)
    | _ -> None in
  let max_steps =
    match field "maxSteps" with
    | None | Some `Null -> Ok (Some default_max_steps)
    | Some (`Int n) when n > 0 -> Ok (Some n)
    | Some _ -> Error (Jsonrpc.Response.Error.Code.InvalidParams, "elpi/run: the parameter maxSteps is not a positive integer") in
  match field "query", field "text", uri, max_steps with
  | _, _, _, Error e -> Error e
  | (None | Some (`Null)), _, _, _ -> Error (InvalidParams, "elpi/run: the parameter query (a string) is missing")
  | Some (`String _), _, None, _ -> Error (InvalidParams, "elpi/run: the parameter textDocument (with its uri) is missing")
  | Some (`String query), Some (`String text), Some uri, Ok max_steps ->
      (* a text that is not a document: a new instance of Elpi *)
      Ok (Runner.run ?max_steps ~instance:(Checker.new_instance ()) ~path:(text_path uri) ~text ~query ())
  | Some (`String query), _, Some uri, Ok max_steps ->
      (match Hashtbl.find_opt documents uri with
       | Some doc -> Ok (Runner.run ?max_steps ~instance:doc.instance ~path:doc.path ~text:doc.text.Text.text ~query ())
       | None -> Error (InvalidParams, "elpi/run: the document is not open, and there is no parameter text"))
  | Some _, _, _, _ -> Error (InvalidParams, "elpi/run: the parameter query is not a string")

let initialized = ref false
let shutdown_received = ref false

(* the result of a request, or an error code and a message *)
let handle_request : type a. a Lsp.Client_request.t -> (a, Jsonrpc.Response.Error.Code.t * string) result = function
  | Initialize params -> initialized := true; Ok (initialize params)
  | _ when not !initialized -> Error (ServerNotInitialized, "initialize was not received")
  | _ when !shutdown_received -> Error (InvalidRequest, "shutdown received")
  | Shutdown -> shutdown_received := true; Ok ()
  | TextDocumentHover params -> Ok (hover params)
  | TextDocumentDefinition params -> Ok (definition params)
  | TextDocumentHighlight params -> Ok (highlight params)
  | SemanticTokensFull params -> Ok (semantic_tokens params)
  | UnknownRequest { meth = "elpi/builtinFile"; params } -> Ok (builtin_file params)
  | UnknownRequest { meth = "elpi/run"; params } -> run params
  | _ -> Error (MethodNotFound, "unsupported request")

(* --- notifications --------------------------------------------------------------- *)

(* an opened or changed document is dirty: it is checked when the user is
   idle *)
let set_text uri version text =
  (match Hashtbl.find_opt documents uri with
   | None ->
       Hashtbl.replace documents uri { path = path_of_uri uri; text = Text.make text; version;
                                       checked = -1; hover = None; instance = Checker.new_instance () }
   | Some doc ->
       doc.text <- Text.make text;
       doc.version <- version;
       doc.hover <- None);
  check_later uri

let handle_notification : Lsp.Client_notification.t -> unit = function
  | Exit -> exit (if !shutdown_received then 0 else 1)
  | _ when not !initialized -> () (* dropped, as the protocol says *)
  | TextDocumentDidOpen { textDocument = { uri; text; version; _ } } -> set_text uri version text
  | TextDocumentDidChange { textDocument = { uri; version }; contentChanges } ->
      (* full synchronization: the last change is the whole text *)
      (match List.rev contentChanges with
       | { text; range = None; _ } :: _ -> set_text uri version text
       | _ -> log "ignoring an incremental change")
  | DidSaveTextDocument { textDocument = { uri }; _ } ->
      (* the other documents may accumulate the saved file (accumulated files
         are read from the disk): they are checked again; the compiled units
         that did not change come from the cache *)
      Hashtbl.iter (fun u (doc : document) ->
          if not (DocumentUri.equal u uri) then begin doc.checked <- -1; check_later u end)
        documents
  | TextDocumentDidClose { textDocument = { uri } } ->
      Hashtbl.remove documents uri;
      Hashtbl.remove dirty uri;
      send_notification (PublishDiagnostics (PublishDiagnosticsParams.create ~uri ~diagnostics:[] ()))
  | Initialized -> ()
  | SetTrace { value } -> Checker.set_trace value
  | CancelRequest _ ->
      (* a request is answered as soon as it is read: none is pending *)
      ()
  | _ -> ()

(* --- messages ---------------------------------------------------------------------- *)

(* handles a message of the client *)
let handle : Jsonrpc.Packet.t -> unit = function
  | Request req ->
      let response =
        match Lsp.Client_request.of_jsonrpc req with
        | Error e -> Jsonrpc.Response.(error req.id (Error.make ~code:InvalidRequest ~message:e ()))
        | Ok (E r) ->
            match handle_request r with
            | Ok x -> Jsonrpc.Response.ok req.id (Lsp.Client_request.yojson_of_result r x)
            | Error (code, message) -> Jsonrpc.Response.(error req.id (Error.make ~code ~message ()))
            | exception e ->
                let message = Printexc.to_string e in
                log "request %s failed: %s" req.method_ message;
                Jsonrpc.Response.(error req.id (Error.make ~code:InternalError ~message ())) in
      send (Jsonrpc.Response.yojson_of_t response)
  | Notification n ->
      (match Lsp.Client_notification.of_jsonrpc n with
       | Ok n -> handle_notification n
       | Error e -> log "ignoring notification %s: %s" n.method_ e)
  | _ -> log "ignoring a message"

(* handles a message as JSON *)
let handle_json json =
  if not !init_called then invalid_arg "Server.handle_json: Server.init was not called";
  match Jsonrpc.Packet.t_of_yojson json with
  | packet -> handle packet
  | exception e -> log "cannot decode message: %s" (Printexc.to_string e)
