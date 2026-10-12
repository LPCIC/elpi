(* Common code of the tests of elpi-lsp: a client that starts the server and
   drives it with JSON-RPC messages, and the printing of a summary of the
   answers. A test is a script, registered with [register], per .elpi file of
   the test directory; [main] runs them all (see test_lsp.ml).
   usage: test_lsp SERVER DIR, where DIR holds the .elpi files of the test *)

open Yojson.Safe.Util

let server, dir =
  match Sys.argv with
  | [| _; s; d |] -> s, d
  | _ -> prerr_endline "usage: test_lsp SERVER DIR"; exit 2

let dir = if Filename.is_relative dir then Filename.concat (Sys.getcwd ()) dir else dir

(* --- progress and timeout ---------------------------------------------------- *)

(* What the test is doing is logged on stderr (the log of the CI), and the
   last thing is remembered: if the test does not terminate in [timeout]
   seconds a watchdog says where it was and stops it, without failing (the
   comparison with the expected output will). *)
let timeout = 180.
let t0 = Unix.gettimeofday ()
let last = ref "starting"
let log fmt =
  Printf.ksprintf (fun s ->
    last := s;
    Printf.eprintf "[test_lsp %6.2fs] %s\n%!" (Unix.gettimeofday () -. t0) s) fmt

let to_server_r, to_server_w = Unix.pipe ~cloexec:true ()
let from_server_r, from_server_w = Unix.pipe ~cloexec:true ()

let pid = Unix.create_process server [| server |] to_server_r from_server_w Unix.stderr
let () = Unix.close to_server_r; Unix.close from_server_w
let oc = Unix.out_channel_of_descr to_server_w
let ic = Unix.in_channel_of_descr from_server_r

let () =
  log "started the server %s (pid %d)" server pid;
  ignore (Thread.create (fun () ->
    Thread.delay timeout;
    Printf.eprintf "[test_lsp] TIMEOUT after %.0fs, the last thing was: %s\n%!" timeout !last;
    (try Unix.kill pid Sys.sigkill with _ -> ());
    exit 0) ())

let send json =
  let s = Yojson.Safe.to_string json in
  Printf.fprintf oc "Content-Length: %d\r\n\r\n%s" (String.length s) s;
  flush oc

let receive () =
  let rec headers len =
    match input_line ic with
    | "\r" | "" -> len
    | l ->
        (match String.split_on_char ':' l with
         | [ k; v ] when String.equal (String.lowercase_ascii k) "content-length" -> headers (int_of_string (String.trim v))
         | _ -> headers len) in
  let len = headers 0 in
  Yojson.Safe.from_string (really_input_string ic len)

let id = ref 0

let request meth params =
  incr id;
  log "request %d: %s" !id meth;
  send (`Assoc ([ "jsonrpc", `String "2.0"; "id", `Int !id; "method", `String meth ]
                @ (match params with `Null -> [] | _ -> [ "params", params ])));
  let rec wait () =
    let m = receive () in
    if Yojson.Safe.equal (member "id" m) (`Int !id) then m else wait () in
  wait ()

let notify meth params =
  log "notification: %s" meth;
  send (`Assoc ([ "jsonrpc", `String "2.0"; "method", `String meth ]
                @ (match params with `Null -> [] | _ -> [ "params", params ])))

(* the files of the test directory, or a file with its path *)
let uri file =
  let path = if Filename.is_relative file then Filename.concat dir file else file in
  (* on Windows C:\a\b is file:///C:/a/b *)
  let path = String.map (fun c -> if Char.equal c '\\' then '/' else c) path in
  "file://" ^ (if not (String.equal path "") && not (Char.equal path.[0] '/') then "/" else "") ^ path
(* replaces [d] by [by] in [s] *)
let replace d by s =
  let b = Buffer.create 80 in
  let n = String.length d in
  let i = ref 0 in
  while !i < String.length s do
    if n > 0 && !i + n <= String.length s && String.equal (String.sub s !i n) d then (Buffer.add_string b by; i := !i + n)
    else (Buffer.add_char b s.[!i]; incr i)
  done;
  Buffer.contents b

(* The server spells the URIs as the editors do, e.g. file:///d%3A/a/b on
   Windows where we write file:///D:/a/b: they are compared decoded and with a
   lowercase drive *)
let normalize_uri u =
  let b = Buffer.create 80 in
  let n = String.length u in
  let rec go i =
    if i < n then
      if Char.equal u.[i] '%' && i + 2 < n + 0 && (match int_of_string_opt ("0x" ^ String.sub u (i + 1) 2) with Some c -> Buffer.add_char b (Char.chr c); true | None -> false)
      then go (i + 3)
      else (Buffer.add_char b u.[i]; go (i + 1)) in
  go 0;
  let u = Buffer.contents b in
  (* file:///D:/... *)
  if String.length u > 10 && String.equal (String.sub u 0 8) "file:///" && Char.equal u.[9] ':'
  then String.sub u 0 8 ^ String.make 1 (Char.lowercase_ascii u.[8]) ^ String.sub u 9 (String.length u - 9)
  else u

let same_uri u1 u2 = String.equal (normalize_uri u1) (normalize_uri u2)

(* the path of a file: URI as the operating system wants it (on Windows
   file:///c%3A/a/b is c:/a/b) *)
let path_of_uri u =
  let u = normalize_uri u in
  let p = Str.global_replace (Str.regexp "^file://") "" u in
  if String.length p > 2 && Char.equal p.[0] '/' && Char.equal p.[2] ':' then String.sub p 1 (String.length p - 1) else p

(* the directory of the test, also as Elpi names it, without _build/default *)
let anonymize s =
  (* the directory as it can be spelled: with / or \, with the drive in
     lowercase (the server does), with a leading / (in a file:/// URI) *)
  let fwd x = String.map (fun c -> if Char.equal c '\\' then '/' else c) x in
  let lower_drive x =
    if String.length x > 1 && Char.equal x.[1] ':' then String.make 1 (Char.lowercase_ascii x.[0]) ^ String.sub x 1 (String.length x - 1) else x in
  let spellings x = [ x; fwd x; lower_drive x; lower_drive (fwd x) ] in
  let clean = Str.global_replace (Str.regexp "[/\\]_build[/\\][^/\\]+") "" dir in
  let dirs = List.concat_map (fun x -> let l = spellings x in l @ List.map (fun y -> "/" ^ y) (List.filter (fun y -> not (String.equal y "") && not (Char.equal y.[0] '/')) (List.map fwd l)))
      [ dir; clean ] in
  (* the longest first: a directory can be a prefix of another *)
  let dirs = List.sort_uniq (fun a b -> match Int.compare (String.length b) (String.length a) with 0 -> String.compare b a | c -> c) dirs in
  (* the URIs of the server encode the colon of the drive *)
  let s = Str.global_replace (Str.regexp_case_fold "%3a") ":" s in
  List.fold_left (fun s d -> replace d "$DIR" s) s dirs
  (* "./" and the separators of Windows after the directory *)
  |> replace "$DIR/./" "$DIR/" |> replace "$DIR\\.\\" "$DIR/" |> replace "$DIR\\" "$DIR/"
  (* the files of the standard library, that the server writes in a temporary directory *)
  |> Str.global_replace (Str.regexp "file://[^ ]*/elpi-lsp-[0-9]+-[0-9a-f]+/") "file://$LIBRARY/"
  (* the instance of Elpi in the URIs of the web server, which depends on how
     many documents were opened before *)
  |> Str.global_replace (Str.regexp "elpi-builtin:/[0-9]+/") "elpi-builtin:/ID/"
  |> Str.global_replace (Str.regexp "\\([a-zA-Z]:\\)?[^ :]*[/\\\\]elpi-lsp-[0-9]+-[0-9a-f]+[/\\\\]") "$LIBRARY/"

let read_file file =
  let ic = open_in_bin (if Filename.is_relative file then Filename.concat dir file else file) in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; s

(* a marker between the steps of the test *)
let first_section = ref true
let section fmt =
  Printf.ksprintf (fun s ->
      (* a blank line between sections *)
      if not !first_section then print_newline ();
      first_section := false;
      Printf.printf "==== %s ====\n" s) fmt

(* the text of a range of a file (of [text] if given), as the lines it covers, quoted; the file is
   given by the uri of the server answer *)
(* the text of [uri]: a file, or a file of the standard library that the web
   server gives as elpi-builtin:/ID/NAME, read with the request elpi/builtinFile *)
let text_of_uri uri =
  let scheme = "elpi-builtin:" in
  if String.length uri > String.length scheme && String.equal (String.sub uri 0 (String.length scheme)) scheme then
    match request "elpi/builtinFile" (`Assoc [ "uri", `String uri ]) |> member "result" with
    | `String s -> s
    | _ -> ""
  else
    try let ic = open_in_bin (path_of_uri uri) in
      let s = really_input_string ic (in_channel_length ic) in close_in ic; s with Sys_error _ -> ""

let snippet ?(underline=false) ?text uri range =
  let text = match text with Some t -> t | None -> text_of_uri uri in
  let lines = Array.of_list (String.split_on_char '\n' text) in
  let pos x = member "line" x |> to_int, member "character" x |> to_int in
  let (l1, c1), (l2, c2) = pos (member "start" range), pos (member "end" range) in
  (* a column in UTF-16 code units to a byte index of the line *)
  let byte_of line col =
    let s = lines.(line) in
    let rec go i u = if u >= col || i >= String.length s then i else
        let c = Char.code s.[i] in
        let n = if c < 0x80 then 1 else if c < 0xE0 then 2 else if c < 0xF0 then 3 else 4 in
        go (i + n) (u + if Int.equal n 4 then 2 else 1) in
    go 0 0 in
  if l1 >= Array.length lines || l2 >= Array.length lines then ""
  else
    List.init (l2 - l1 + 1) (fun i ->
        let line = l1 + i in
        let s = lines.(line) in
        let b = if Int.equal line l1 then byte_of line c1 else 0 in
        let e = if Int.equal line l2 then byte_of line c2 else String.length s in
        if not underline then "    | " ^ String.sub s b (e - b)
        else begin
          (* the whole line, and the selected columns underlined *)
          let chars s = (* number of code points *)
            let n = ref 0 in String.iter (fun c -> if not (Int.equal (Char.code c land 0xC0) 0x80) then incr n) s; !n in
          let pad = Buffer.create 16 in
          String.iter (fun c ->
              if not (Int.equal (Char.code c land 0xC0) 0x80) then Buffer.add_char pad (if Char.equal c '\t' then c else ' '))
            (String.sub s 0 b);
          let pad = Buffer.contents pad in
          let width = max 1 (chars (String.sub s b (e - b))) in
          "    | " ^ s ^ "\n    | " ^ pad ^ String.make width '^'
        end) |> String.concat "\n"

let pp_range r =
  let p x = Printf.sprintf "%d:%d" (member "line" x |> to_int) (member "character" x |> to_int) in
  p (member "start" r) ^ "-" ^ p (member "end" r)

let severity = function 1 -> "error" | 2 -> "warning" | 3 -> "info" | _ -> "hint"

(* the last text sent for each file *)
let sent : (string, string) Hashtbl.t = Hashtbl.create 7

(* the diagnostics published for a file *)
let rec wait_publish file =
  log "waiting for the diagnostics of %s" file;
  let m = receive () in
  if Yojson.Safe.equal (member "method" m) (`String "textDocument/publishDiagnostics") then begin
    let got = member "params" m |> member "uri" |> to_string in
    if same_uri got (uri file) then
      member "params" m |> member "version",
      member "params" m |> member "diagnostics" |> to_list
    else begin
      log "ignored the diagnostics of %s (%d), expected the ones of %s"
        got (member "params" m |> member "diagnostics" |> to_list |> List.length) (uri file);
      wait_publish file
    end
  end else wait_publish file

let wait_diagnostics file =
  let version, ds = wait_publish file in
  Printf.printf "diagnostics of %s%s: %d\n" (anonymize file)
    (match version with `Int v -> Printf.sprintf " (version %d)" v | _ -> "") (List.length ds);
  List.iter (fun d ->
      Printf.printf "  %s %s: %s\n" (pp_range (member "range" d))
        (severity (member "severity" d |> to_int)) (anonymize (member "message" d |> to_string));
      let range = member "range" d in
      if not (Yojson.Safe.equal (member "start" range) (member "end" range)) then
        print_endline (snippet ~underline:true ~text:(Hashtbl.find sent file) (uri file) range))
    ds

let open_file file =
  section "open %s" (anonymize file);
  Hashtbl.replace sent file (read_file file);
  notify "textDocument/didOpen" (`Assoc [ "textDocument", `Assoc [
      "uri", `String (uri file); "languageId", `String "elpi"; "version", `Int 1;
      "text", `String (read_file file) ] ]);
  wait_diagnostics file

let change_file file version text =
  section "change %s (version %d)" file version;
  Hashtbl.replace sent file text;
  notify "textDocument/didChange" (`Assoc [
      "textDocument", `Assoc [ "uri", `String (uri file); "version", `Int version ];
      "contentChanges", `List [ `Assoc [ "text", `String text ] ] ]);
  wait_diagnostics file

let change_file_burst file first_version texts =
  section "change %s, %d changes in a row" file (List.length texts);
  List.iteri (fun i text ->
      Hashtbl.replace sent file text;
      notify "textDocument/didChange" (`Assoc [
          "textDocument", `Assoc [ "uri", `String (uri file); "version", `Int (first_version + i) ];
          "contentChanges", `List [ `Assoc [ "text", `String text ] ] ])) texts;
  wait_diagnostics file

(* the LSP position of the [k]-th character after the first occurrence of
   [needle] in [file], counting columns in UTF-16 code units *)
let position file needle k =
  let s = read_file file in
  let rec find i = if String.equal (String.sub s i (String.length needle)) needle then i else find (i + 1) in
  let off = find 0 + k in
  let line = ref 0 and col = ref 0 in
  for i = 0 to off - 1 do
    let c = Char.code s.[i] in
    if Char.equal s.[i] '\n' then (incr line; col := 0)
    else if not (Int.equal (c land 0xC0) 0x80) then col := !col + (if c >= 0xF0 then 2 else 1)
  done;
  `Assoc [ "line", `Int !line; "character", `Int !col ]

let at file needle k =
  `Assoc [ "textDocument", `Assoc [ "uri", `String (uri file) ]; "position", position file needle k ]

let pos_of x = member "line" x |> to_int, member "character" x |> to_int

(* Shows the lines of [file] where there is something to show, each followed by
   one row of marks per kind of thing (the label of the row, the mark, the
   ranges as (line, column, line, column)): so that it is visible where the
   cursor is and what is highlighted. *)
let show_marks file rows =
  let lines = Array.of_list (String.split_on_char '\n' (read_file file)) in
  let width = List.fold_left (fun w (label, _, _) -> max w (String.length label)) 10 rows in
  let involved = List.sort_uniq Int.compare
      (List.concat_map (fun (_, _, ranges) ->
         List.concat_map (fun (l1, _, l2, _) -> List.init (l2 - l1 + 1) (fun i -> l1 + i)) ranges) rows) in
  List.iter (fun line ->
      Printf.printf "  line %d:\n    %-*s | %s\n" line width "" lines.(line);
      List.iter (fun (label, mark, ranges) ->
          let b = Bytes.make (String.length lines.(line) + 1) ' ' in
          List.iter (fun (l1, c1, l2, c2) ->
              if l1 <= line && line <= l2 then begin
                let c1 = if Int.equal line l1 then c1 else 0 and c2 = if Int.equal line l2 then c2 else String.length lines.(line) in
                for c = c1 to max c1 (c2 - 1) do if c < Bytes.length b then Bytes.set b c mark done
              end) ranges;
          let marks = String.trim (Bytes.to_string b) in
          if not (String.equal marks "") then begin
            let n = ref (Bytes.length b) in
            while !n > 0 && Char.equal (Bytes.get b (!n - 1)) ' ' do decr n done;
            Printf.printf "    %-*s | %s\n" width label (Bytes.sub_string b 0 !n)
          end) rows)
    involved

let cursor_row file needle k =
  let l, c = pos_of (position file needle k) in
  "cursor", '*', [ (l, c, l, c + 1) ]

let cursor_text file needle k =
  let l, c = pos_of (position file needle k) in
  Printf.sprintf "(the cursor is at %d:%d)" l c

let range_of x = let l1, c1 = pos_of (member "start" x) and l2, c2 = pos_of (member "end" x) in (l1, c1, l2, c2)

let hover file needle k =
  let r = request "textDocument/hover" (at file needle k) |> member "result" in
  if (match r with `Null -> true | _ -> false) then begin
    Printf.printf "hover %S+%d %s: none\n" needle k (cursor_text file needle k);
    show_marks file [ cursor_row file needle k ]
  end
  else begin
    let range = member "range" r in
    Printf.printf "hover %S+%d %s: %s\n" needle k (cursor_text file needle k) (pp_range range);
    show_marks file [ "hovered", '^', [ range_of range ]; cursor_row file needle k ];
    (* the text of the popup *)
    String.split_on_char '\n' (member "contents" r |> member "value" |> to_string)
    |> List.iter (fun l -> Printf.printf "    ? %s\n" l)
  end

let definition ?none file needle k =
  let r = request "textDocument/definition" (at file needle k) |> member "result" in
  Printf.printf "definition %S+%d %s:" needle k (cursor_text file needle k);
  match r with
  | `Null | `List [] ->
      (* why there is no answer is what the script knows *)
      print_endline (match none with None -> " none" | Some why -> " none (" ^ why ^ ")");
      show_marks file [ cursor_row file needle k ]
  | `List (l :: _) | (`Assoc _ as l) ->
      print_newline ();
      show_marks file [ cursor_row file needle k ];
      (* a LocationLink (the client announces linkSupport): where the client
         jumps (targetSelectionRange), and what it previews (targetRange) *)
      (match member "targetUri" l with
       | `String uri ->
           let range = member "targetSelectionRange" l and preview = member "targetRange" l in
           Printf.printf "  defined at %s %s\n%s\n" (anonymize uri) (pp_range range) (snippet uri range);
           Printf.printf "  previewed %s\n%s\n" (pp_range preview) (snippet uri preview)
       | _ ->
           let uri = member "uri" l |> to_string and range = member "range" l in
           Printf.printf "  defined at %s %s\n%s\n" (anonymize uri) (pp_range range) (snippet uri range))
  | _ -> print_endline " ?"

(* the file where the definition of the symbol at the position is, if it is
   a file of the disk *)
let definition_file file needle k =
  match request "textDocument/definition" (at file needle k) |> member "result" with
  | `List (l :: _) | (`Assoc _ as l) ->
      let uri = match member "targetUri" l with `String u -> u | _ -> member "uri" l |> to_string in
      if String.length uri > 7 && String.equal (String.sub uri 0 7) "file://" then Some (path_of_uri uri) else None
  | _ -> None

let is_read_only path = (try Unix.access path [ Unix.W_OK ]; false with Unix.Unix_error _ -> true)

(* The highlights of the variable or constant at the position: its definition
   site (the binder of a variable) and its occurrences (the server says write
   and read), shown with the cursor. *)
let highlight file needle k =
  let r = request "textDocument/documentHighlight" (at file needle k) |> member "result" in
  Printf.printf "highlight %S+%d %s:\n" needle k (cursor_text file needle k);
  match r with
  | `Null | `List [] ->
      print_endline "  none (the cursor is not on a variable or a constant)";
      show_marks file [ cursor_row file needle k ]
  | `List l ->
      let highlights = List.map (fun h ->
          (match member "kind" h with `Int 3 -> `Binder | _ -> `Occurrence), range_of (member "range" h)) l in
      List.iter (fun (kind, (l1, c1, l2, c2)) ->
          Printf.printf "  %s %d:%d-%d:%d\n" (match kind with `Binder -> "definition" | `Occurrence -> "occurrence") l1 c1 l2 c2)
        highlights;
      let same_kind k kind = match k, kind with `Binder, `Binder | `Occurrence, `Occurrence -> true | _ -> false in
      let ranges kind = List.filter_map (fun (k, r) -> if same_kind k kind then Some r else None) highlights in
      show_marks file [ "definition", '=', ranges `Binder; "occurrence", '^', ranges `Occurrence; cursor_row file needle k ]
  | _ -> print_endline "  ?"

(* the types of tokens of the server, from its capabilities *)
let token_types = ref []

(* The colors of the file: the lines where there are tokens, with a row of
   marks for each type of token (^) and one for the binders, that have the
   modifier declaration (=). *)
let semantic_tokens file =
  let r = request "textDocument/semanticTokens/full" (`Assoc [ "textDocument", `Assoc [ "uri", `String (uri file) ] ]) |> member "result" in
  let data = match member "data" r with `List l -> List.map to_int l | _ -> [] in
  let rec decode line col = function
    | dl :: dc :: len :: t :: m :: rest ->
        let line = line + dl in
        let col = if Int.equal dl 0 then col + dc else dc in
        (line, col, len, List.nth !token_types t, not (Int.equal m 0)) :: decode line col rest
    | _ -> [] in
  let tokens = decode 0 0 data in
  print_endline "semantic tokens (^ the token, = a declaration):";
  let rows = List.concat_map (fun t ->
      List.filter_map (fun declaration ->
          let ranges = List.filter_map (fun (l, c, len, t', d) -> if String.equal t' t && Bool.equal d declaration then Some (l, c, l, c + len) else None) tokens in
          if ranges = [] then None else Some ((if declaration then t ^ " decl" else t), (if declaration then '=' else '^'), ranges))
        [ false; true ]) !token_types in
  if rows = [] then print_endline "  none" else show_marks file rows

(* --- scripts ---------------------------------------------------------------- *)

(* closes a file; the server then publishes no diagnostics for it *)
let close_file file =
  notify "textDocument/didClose" (`Assoc [ "textDocument", `Assoc [ "uri", `String (uri file) ] ]);
  ignore (wait_publish file)

(* [register ~name file script]: [script file] is run by [main] when all the
   scripts have been registered, in the order of their (unique) names. It
   opens [file] and queries the server; [main] closes [file] afterwards, so
   that each script starts from a clean document. By convention [name] is the
   name of [file] without .elpi, followed by something if there are several
   scripts for the same file. *)
let scripts : (string * string * (string -> unit)) list ref = ref []

let register ~name file script =
  if List.exists (fun (n, _, _) -> String.equal n name) !scripts then
    failwith ("two scripts are named " ^ name);
  scripts := (name, file, script) :: !scripts

(* Runs [f] with the standard output redirected to [file] *)
let with_stdout_to file f =
  first_section := true;
  flush stdout;
  let saved = Unix.dup Unix.stdout in
  let fd = Unix.openfile file [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o644 in
  Unix.dup2 fd Unix.stdout;
  Unix.close fd;
  Fun.protect f ~finally:(fun () ->
      flush stdout;
      Unix.dup2 saved Unix.stdout;
      Unix.close saved)

(* The output of the script [name] is written to [name].output (in the
   directory of the test), to be
   compared with [name].expected. The standard output has the rest: the
   capabilities of the server and its shutdown. The scripts named in the
   environment variable TEST_LSP_SKIP (separated by commas) are not run. *)
let main () =
  let skip = String.split_on_char ',' (Option.value ~default:"" (Sys.getenv_opt "TEST_LSP_SKIP")) in
  (* a request before initialize is an error *)
  let early = request "textDocument/hover" (`Assoc [
      "textDocument", `Assoc [ "uri", `String (uri "good.elpi") ];
      "position", `Assoc [ "line", `Int 0; "character", `Int 0 ] ]) in
  Printf.printf "before initialize: error %s\n"
    (Yojson.Safe.to_string (member "error" early |> member "code"));
  (* the client takes LocationLinks for definitions, as VS Code does *)
  let capabilities = `Assoc [ "textDocument", `Assoc [ "definition", `Assoc [ "linkSupport", `Bool true ] ] ] in
  let init = request "initialize" (`Assoc [ "processId", `Null; "rootUri", `Null; "capabilities", capabilities ]) in
  let caps = init |> member "result" |> member "capabilities" in
  token_types := (try member "semanticTokensProvider" caps |> member "legend" |> member "tokenTypes" |> to_list |> List.map to_string with _ -> []);
  Printf.printf "capabilities: %s\n" (Yojson.Safe.to_string caps);
  notify "initialized" (`Assoc []);
  List.iter (fun (name, file, script) ->
      log "script %s (%s)" name file;
      with_stdout_to (Filename.concat dir (name ^ ".output")) (fun () -> script file; close_file file);
      log "script %s done" name)
    (List.sort (fun (n1, _, _) (n2, _, _) -> String.compare n1 n2)
       (List.filter (fun (n, _, _) -> not (List.exists (String.equal n) skip)) !scripts));
  let r = request "shutdown" `Null in
  Printf.printf "shutdown: %s\n" (Yojson.Safe.to_string (member "result" r));
  notify "exit" `Null;
  log "waiting for the server to exit";
  match Unix.waitpid [] pid with
  | _, Unix.WEXITED n -> Printf.printf "server exited with code %d\n" n
  | _ -> print_endline "server killed"

let run ?file ?text ?max_steps query =
  section "run %s%s%s" query (match file, text with _, Some _ -> " on a text" | Some f, None -> " on " ^ f | None, None -> "")
    (match max_steps with Some n -> " (maxSteps " ^ Yojson.Safe.to_string n ^ ")" | None -> "");
  let params =
    (match file with Some f -> [ "textDocument", `Assoc [ "uri", `String (uri f) ] ] | None -> [])
    @ (match text with Some t -> [ "text", `String t ] | None -> [])
    @ (match max_steps with Some n -> [ "maxSteps", n ] | None -> [])
    @ [ "query", `String query ] in
  let r = request "elpi/run" (`Assoc params) in
  match member "result" r with
  | `Assoc _ as res ->
      Printf.printf "status: %s\n" (member "status" res |> to_string);
      let lines prefix s =
        String.split_on_char '\n' (String.trim s) |> List.iter (fun l -> Printf.printf "  %s %s\n" prefix l) in
      (match member "output" res |> to_string with "" -> () | s -> lines "|" s);
      List.iter (fun e -> lines "!" (anonymize (to_string e))) (member "errors" res |> to_list);
      List.iter (fun e -> lines "#" (anonymize (to_string e))) (member "diagnostics" res |> to_list);
      (match member "assignments" res with
       | `Assoc l -> List.iter (fun (name, v) -> lines "=" (name ^ " = " ^ to_string v)) l
       | _ -> ());
      (match member "constraints" res with
       | `List cs -> List.iter (fun c -> lines "?" (to_string c)) cs
       | _ -> ())
  | _ -> Printf.printf "error: %s\n" (member "error" r |> member "message" |> to_string)
