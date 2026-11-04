(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_lexer_config

exception ParseError = Parser_config.ParseError

module type Parser = sig
  val goal : loc:Util.Loc.t -> text:string -> Ast.Goal.t
  val goal_from : loc:Util.Loc.t -> Lexing.lexbuf -> Ast.Goal.t
  (* the same, but a syntax error is returned instead of being raised as
     ParseError, with the warnings *)
  val query : loc:Util.Loc.t -> text:string -> (Ast.Goal.t, Util.error) result * Util.warning list
  val query_from : loc:Util.Loc.t -> Lexing.lexbuf -> (Ast.Goal.t, Util.error) result * Util.warning list

  val program_from : ?max_errors:int -> loc:Util.Loc.t -> digest:Digest.t -> Lexing.lexbuf ->
    Ast.Program.t * Util.error list * Util.warning list
  val program : ?max_errors:int -> string -> Ast.Program.t * Util.error list * Util.warning list
end

module type Parser_w_Internals = sig
  include Parser

  module Internal : sig
    val infix_SYMB : (Lexing.lexbuf -> Tokens.token) -> Lexing.lexbuf -> Ast.Func.t
    val prefix_SYMB : (Lexing.lexbuf -> Tokens.token) -> Lexing.lexbuf -> Ast.Func.t
    val postfix_SYMB : (Lexing.lexbuf -> Tokens.token) -> Lexing.lexbuf -> Ast.Func.t
  end
end

module type Config = sig
  val versions : (int * int * int) Util.StrMap.t
  val resolver : ?cwd:string -> unit:string -> unit -> string
  (* the text of a file; raises Failure if it cannot be read *)
  val reader : string -> string

end

(* the name of a file in the locations of its contents *)
let cleanup_fname filename = Re.Str.replace_first (Re.Str.regexp "/_build/[^/]+") "" filename

module Make(C : Config) = struct
  
let parse_ref : (?cwd:string -> string -> Ast.Program.t) ref =
  ref (fun ?cwd:_ _ -> assert false)

(* a file to accumulate that cannot be found: the message of the resolver *)
exception Cannot_resolve_accumulated_file of string

(* the warnings found while parsing a program *)
module Warnings : sig
  val init : unit -> unit
  val add : Util.warning -> unit
  val consume : unit -> Util.warning list  (* in order, and forgets them *)
end = struct
  let warnings : Util.warning list ref = ref [] (* most recent first *)
  let init () = warnings := []
  let add w = warnings := w :: !warnings
  let consume () = let ws = List.rev !warnings in warnings := []; ws
end

(* the errors found while parsing a program: until there are max_errors of
   them, an error is recorded and the parser goes on, then it stops (with
   max_errors = 0 the first error is raised) *)
module Errors : sig
  val init : max_errors:int -> unit
  val max_errors_reached : unit -> bool
  val add : Util.Loc.t * string -> unit
  val consume : unit -> (Util.Loc.t * string) list  (* in order, and forgets them *)
end = struct
  let max_errors = ref 0
  let count = ref 0
  let errors : (Util.Loc.t * string) list ref = ref [] (* most recent first *)
  let init ~max_errors:n = max_errors := n; count := 0; errors := []
  let max_errors_reached () = !count >= !max_errors
  let add e = incr count; errors := e :: !errors
  let consume () = let es = List.rev !errors in errors := []; es
end

module DocComments : sig
  val with_comments : (unit -> 'a) -> 'a
  val add : Lexing.position -> Lexing.position -> unit
  val add_trailing : Lexing.position -> Lexing.position -> unit
  val token_read : fullstop:bool -> Lexing.position -> unit
  val before : Util.Loc.t -> Util.Loc.t option
  val after : unit -> Util.Loc.t option
end = struct
  type block = { start : Lexing.position; stop : Lexing.position }

  (* by file and last line *)
  let blocks : (string * int, block) Hashtbl.t = Hashtbl.create 17

  (* the line comment after the last full stop, on its line (e.g. symb ok :
     diagnostic. % Success): the lexer reads it with the full stop, so it is
     there when the declaration that the full stop ends is built; the next
     token drops it *)
  let trailing : block option ref = ref None
  let active = ref false

  (* the file and the line where the last token ends: a comment on that line
     follows code, it is not documentation (e.g. pred p. % about p) *)
  let last_token : (string * int) option ref = ref None
  let token_read ~fullstop (p : Lexing.position) =
    if not fullstop then trailing := None;
    last_token := Some (p.pos_fname, p.pos_lnum)
  let follows_code (p : Lexing.position) =
    match !last_token with
    | Some (f, l) -> String.equal f p.pos_fname && Int.equal l p.pos_lnum
    | None -> false

  let reset () = Hashtbl.reset blocks; trailing := None; last_token := None

  let with_comments f =
    if !active then f ()
    else begin
      reset ();
      active := true;
      Fun.protect f ~finally:(fun () -> active := false; reset ())
    end

  let add (start : Lexing.position) (stop : Lexing.position) =
    if !active && not (follows_code start) then
    let previous = start.pos_fname, start.pos_lnum - 1 in
    let start =
      match Hashtbl.find_opt blocks previous with
      | Some b -> Hashtbl.remove blocks previous; b.start
      | None -> start in
    Hashtbl.replace blocks (stop.pos_fname, stop.pos_lnum) { start; stop }

  let add_trailing start stop = if !active then trailing := Some { start; stop }

  let to_loc { start; stop } =
    { Util.Loc.client_payload = None; source_name = start.pos_fname;
      source_start = start.pos_cnum; source_stop = stop.pos_cnum;
      line = start.pos_lnum; line_starts_at = start.pos_bol }

  let before (loc : Util.Loc.t) =
    Hashtbl.find_opt blocks (loc.source_name, loc.line - 1) |> Option.map to_loc

  let after () = Option.map to_loc !trailing
end


module ParseFile = struct
  (* until max_errors is reached, a file that cannot be found or parsed is
     one with no contents (the error is recorded), so that the program still
     depends on it. Its digest is not the one of a text, which a file with
     contents has. Then the error goes up to the parser, which stops. *)
  let parse_accumulated_file ~loc ?cwd file =
    let empty file_name = { Ast.file_name; digest = Digest.string ("not parsed " ^ file_name); deps = []; ast = [] } in
    match !parse_ref ?cwd file with
    | p -> p
    | exception Cannot_resolve_accumulated_file msg when not (Errors.max_errors_reached ()) ->
        Errors.add (loc, msg);
        empty (match cwd with Some d when Filename.is_relative file -> Filename.concat d file | _ -> file)
    | exception Parser_config.ParseError (l, msg) when not (Errors.max_errors_reached ()) ->
        Errors.add (l, msg);
        empty (C.resolver ?cwd ~unit:file ())
  let client_payload : Obj.t option ref = ref None
  let set_current_clent_loc_pyload x = client_payload := Some x
  let get_current_client_loc_payload () = !client_payload
  let warn = Warnings.add
  let add_comment = DocComments.add
  let doc_before = DocComments.before
  let doc_after_dot = DocComments.after

end

module Grammar = Grammar.Make(ParseFile)
  
let message_of_state s = try Error_messages.message s with Not_found -> "syntax error"

let raise_parse_error lexbuf stateid =
  let message = message_of_state stateid in
  let loc = lexbuf.Lexing.lex_curr_p in
  let loc = {
    Util.Loc.client_payload = None;
    source_name = loc.Lexing.pos_fname;
    line = loc.Lexing.pos_lnum;
    line_starts_at = loc.Lexing.pos_bol;
    source_start = loc.Lexing.pos_cnum;
    source_stop = loc.Lexing.pos_cnum;
  } in
  raise (Parser_config.ParseError(loc,message))

(* the lexer records the comments, for the documentation *)
let lexer_config =
  Lexer.config ~comment:ParseFile.add_comment ~trailing_comment:DocComments.add_trailing C.versions

(* the lexer, telling DocComments where each token ends *)
let token lexbuf =
  let t = Lexer.token lexer_config lexbuf in
  DocComments.token_read ~fullstop:(match t with Tokens.FULLSTOP -> true | _ -> false) lexbuf.Lexing.lex_curr_p;
  t

let parse ?(lexer=token) grammar lexbuf =
  let buffer, lexer = MenhirLib.ErrorReports.wrap lexer in
  try
    Grammar.MenhirInterpreter.loop_handle
     (fun x -> x)
     (function (HandlingError e) -> raise_parse_error lexbuf Grammar.MenhirInterpreter.(current_state_number e) | _ -> assert false)
     (Grammar.MenhirInterpreter.lexer_lexbuf_to_supplier lexer lexbuf)
     (grammar lexbuf.lex_curr_p)
    (* grammar lexer lexbuf *)
  with
  | Ast.Term.NotInProlog(loc,message) ->
      raise (Parser_config.ParseError(loc,message^"\n"))
  | Lexer.Error(loc,message) ->
    let loc = {
      Util.Loc.client_payload = None;
      source_name = loc.Lexing.pos_fname;
      line = loc.Lexing.pos_lnum;
      line_starts_at = loc.Lexing.pos_bol;
      source_start = loc.Lexing.pos_cnum;
      source_stop = loc.Lexing.pos_cnum;
    } in
    raise (Parser_config.ParseError(loc,message))
  | Lexer.Unexpected_character p ->
    let loc = {
      Util.Loc.client_payload = None;
      source_name = p.Lexing.pos_fname;
      line = p.Lexing.pos_lnum;
      line_starts_at = p.Lexing.pos_bol;
      source_start = p.Lexing.pos_cnum;
      source_stop = p.Lexing.pos_cnum + 1;
    } in
    raise (Parser_config.ParseError(loc,"unexpected character"))
  (* | Grammar.Error stateid -> raise_parse_error lexbuf stateid *)

let already_parsed = Hashtbl.create 11

(* the text of a .sig file, if there is one (Teyjus compatibility) *)
let read_sig f = try Some (C.reader f) with Failure _ -> None

let parse_file_contents ~filename text =
  let digest = Digest.string text in
  if Hashtbl.mem already_parsed digest then
    Hashtbl.find already_parsed digest
  else
    let lexbuf = Lexing.from_string text in
    let dest = cleanup_fname filename in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = dest };
    let ast = parse Grammar.Incremental.program lexbuf in
    let output = { Ast.file_name = filename; deps = []; digest; ast } in
    Hashtbl.add already_parsed digest output;
    output

let () =
  parse_ref := (fun ?cwd filename ->
  let filename =
    try C.resolver ?cwd ~unit:filename ()
    with Failure msg -> raise (Cannot_resolve_accumulated_file msg) in
  let text = C.reader filename in
  if String.equal (Filename.extension filename) ".mod" then
    (* Teyjus compatibility *)
    let sig_filename = Filename.chop_extension filename ^ ".sig" in
    match read_sig sig_filename with
    | Some sig_text ->
      let s = parse_file_contents ~filename:sig_filename sig_text in
      let m = parse_file_contents ~filename text in
      { Ast.file_name = filename; digest = Digest.string (s.digest ^ m.digest); deps = []; ast = s.ast @ m.ast  }
    | None -> parse_file_contents ~filename text
  else parse_file_contents ~filename text)

let to_lexing_loc { Util.Loc.source_name; line; line_starts_at; source_start; _ } =
  { Lexing.pos_fname = source_name;
    pos_lnum = line;
    pos_bol = line_starts_at;
    pos_cnum = source_start; }
  
let lexing_set_position lexbuf loc =
  Option.iter ParseFile.set_current_clent_loc_pyload loc.Util.Loc.client_payload;
  let loc = to_lexing_loc loc in
  let open Lexing in
  lexbuf.lex_abs_pos <- loc.pos_cnum;
  lexbuf.lex_start_p <- loc;
  lexbuf.lex_curr_p <- loc
  
let to_loc lexbuf =
  let p = lexbuf.Lexing.lex_start_p in
  { Util.Loc.client_payload = None; source_name = p.pos_fname; line = p.pos_lnum;
    line_starts_at = p.pos_bol; source_start = p.pos_cnum; source_stop = lexbuf.Lexing.lex_curr_p.pos_cnum }

let goal_from ~loc lexbuf =
  lexing_set_position lexbuf loc;
  parse Grammar.Incremental.goal lexbuf
      
let goal ~loc ~text =
  let lexbuf = Lexing.from_string text in
  goal_from ~loc lexbuf

let at_eof lexbuf = lexbuf.Lexing.lex_curr_pos >= lexbuf.Lexing.lex_buffer_len

(* skips the character that the lexer could not recognize *)
let skip_char lexbuf =
  let open Lexing in
  lexbuf.lex_curr_pos <- lexbuf.lex_curr_pos + 1;
  lexbuf.lex_start_pos <- lexbuf.lex_curr_pos;
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_cnum = lexbuf.lex_curr_p.pos_cnum + 1 };
  lexbuf.lex_start_p <- lexbuf.lex_curr_p

(* an error of the parser *)
let make_error (loc, message) = { Util.component = "Parser"; loc = Some loc; message }

let query_from ~loc lexbuf =
  Warnings.init ();
  let q =
    match goal_from ~loc lexbuf with
    | g -> Ok g
    | exception Parser_config.ParseError (loc, message) -> Error (make_error (loc, message)) in
  q, Warnings.consume ()

let query ~loc ~text = query_from ~loc (Lexing.from_string text)

let program_from ?(max_errors = max_int) ~loc:start_loc ~digest lexbuf =
  DocComments.with_comments @@ fun () ->
  Hashtbl.clear already_parsed;
  Warnings.init ();
  let token = token in

  lexing_set_position lexbuf start_loc;

  (* set by the lexer or skip *)
  let last_token_lexed = ref None in
  let first_token_lexed_loc = ref None in

  let lexer lexbuf =
    let t = token lexbuf in
    last_token_lexed := Some t;
    if Option.is_none !first_token_lexed_loc then
      first_token_lexed_loc := Some lexbuf.Lexing.lex_start_p;
    t in

  (* skips up to the next dot (or the end of the text); nothing to skip if the
     last token read is one of them *)
  let rec skip () =
    match !last_token_lexed with
    | Some (Tokens.FULLSTOP | Tokens.EOF) -> ()
    | _ ->
        let pos = lexbuf.Lexing.lex_curr_pos in
        match lexer lexbuf with
        | _ -> skip ()
        | exception (Lexer.Error _ | Lexer.Unexpected_character _) ->
            (* the lexer must make progress, otherwise the character is skipped *)
            if lexbuf.Lexing.lex_curr_pos > pos then skip ()
            else if at_eof lexbuf then last_token_lexed := Some Tokens.EOF
            else (skip_char lexbuf; skip ()) in

  (* the span of the declaration being parsed, up to where the error was
     found *)
  let declaration_loc () =
    let loc = to_loc lexbuf in
    match !first_token_lexed_loc with
    | Some p -> { loc with Util.Loc.source_start = p.pos_cnum; line = p.pos_lnum; line_starts_at = p.pos_bol }
    | None -> loc in

  (* the parser stops: nothing is dropped silently *)
  let stop declarations =
    Errors.add (to_loc lexbuf, Printf.sprintf "too many errors (limit %d): the rest was not parsed, the result is incomplete" max_errors);
    declarations in

  (* the declarations (most recent first); the errors are in Errors *)
  let rec loop declarations =
    last_token_lexed := None; first_token_lexed_loc := None;
    (* an error: it is recorded, the rest of the declaration is skipped *)
    let recover (loc, msg) =
      if max_errors = 0 then raise (Parser_config.ParseError (loc, msg));
      if Errors.max_errors_reached () then stop declarations
      else begin
        Errors.add (loc, msg);
        skip ();
        match !last_token_lexed with
        | Some Tokens.EOF -> declarations
        | _ -> loop declarations
      end in
    if max_errors > 0 && Errors.max_errors_reached () then stop declarations
    else
    match parse ~lexer Grammar.Incremental.one_decl lexbuf with
    | Some d -> loop (d :: declarations)
    | None -> declarations
    | exception Parser_config.ParseError (loc, msg) when not (String.equal loc.Util.Loc.source_name start_loc.Util.Loc.source_name) ->
        (* an error in an accumulated file: it is reported on the accumulate
           directive, with the position in the file *)
        recover (declaration_loc (),
          Printf.sprintf "in %s, line %d, column %d: %s" loc.source_name loc.line
            (loc.source_start - loc.line_starts_at + 1) msg)
    | exception Parser_config.ParseError (loc, msg) ->
        (* the error is reported just after the offending token, that is the
           last one read: the error is made to cover it *)
        recover ((if loc.Util.Loc.source_start = loc.source_stop
                     && loc.source_stop = lexbuf.Lexing.lex_curr_p.pos_cnum
                  then to_loc lexbuf else loc), msg)
    | exception Cannot_resolve_accumulated_file msg -> recover (declaration_loc (), msg) in
  Errors.init ~max_errors;
  let declarations = loop [] in
  let errors = Errors.consume () in
  let ast = List.rev declarations in
  let filename = let open Util.Loc in
    Printf.sprintf "%s:%d:%d" start_loc.source_name start_loc.source_stop lexbuf.Lexing.lex_curr_pos in
  let ws = Warnings.consume () in
  { Ast.file_name = filename; deps = []; digest; ast },
  List.map make_error errors,
  ws

(* a file, with its .sig if it is a .mod (as parse_ref does) *)
let program ?max_errors file =
  Hashtbl.clear already_parsed;
  let filename = C.resolver ~unit:file () in
  let one f text =
    let dest = cleanup_fname f in
    let p, errors, warnings = program_from ?max_errors ~loc:(Util.Loc.initial dest) ~digest:(Digest.string text) (Lexing.from_string text) in
    { p with Ast.file_name = f }, errors, warnings in
  if String.equal (Filename.extension filename) ".mod" then begin
    let sig_filename = Filename.chop_extension filename ^ ".sig" in
    match read_sig sig_filename with
    | Some sig_text ->
      let s, es, ws = one sig_filename sig_text in
      let m, em, wm = one filename (C.reader filename) in
      { Ast.file_name = filename; digest = Digest.string (s.Ast.digest ^ m.Ast.digest); deps = []; ast = s.ast @ m.ast }, es @ em, ws @ wm
    | None -> one filename (C.reader filename)
  end else one filename (C.reader filename)


module Internal = struct
let infix_SYMB = Grammar.infix_SYMB
let prefix_SYMB = Grammar.prefix_SYMB
let postfix_SYMB = Grammar.postfix_SYMB
end

end