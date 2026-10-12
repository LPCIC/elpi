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

end

(* the name of a file in the locations of its contents *)
let cleanup_fname filename = Re.Str.replace_first (Re.Str.regexp "/_build/[^/]+") "" filename

module Make(C : Config) = struct
  
let parse_ref : (?cwd:string -> string -> Ast.Program.t) ref =
  ref (fun ?cwd:_ _ -> assert false)

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


module ParseFile = struct
  let parse_file ?cwd file = !parse_ref ?cwd file
  let client_payload : Obj.t option ref = ref None
  let set_current_clent_loc_pyload x = client_payload := Some x
  let get_current_client_loc_payload () = !client_payload
  let warn = Warnings.add

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

let parse ?(lexer=Lexer.(token C.versions)) grammar lexbuf =
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

let parse_one_file digest filename =
  if Hashtbl.mem already_parsed digest then
    Hashtbl.find already_parsed digest
  else 
    let ic = open_in filename in
    Fun.protect ~finally:(fun () -> close_in ic) @@ fun () ->
    let lexbuf = Lexing.from_channel ic in
    let dest = cleanup_fname filename in
    lexbuf.Lexing.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = dest };
    let ast = parse Grammar.Incremental.program lexbuf in
    let output = { Ast.file_name = filename; deps = []; digest; ast } in
    Hashtbl.add already_parsed digest output;
    output

(* a file to accumulate that cannot be found: the message of the resolver *)
exception Cannot_accumulate of string

let () =
  parse_ref := (fun ?cwd filename ->
  let filename =
    try C.resolver ?cwd ~unit:filename ()
    with Failure msg -> raise (Cannot_accumulate msg) in
  let digest = Digest.file filename in
  if String.equal (Filename.extension filename) ".mod" then
    (* Teyjus compatibility *)
    let sig_filename = Filename.chop_extension filename ^ ".sig" in
    if Sys.file_exists sig_filename then
      let ds = Digest.file sig_filename in
      let s = parse_one_file ds sig_filename in
      let m = parse_one_file digest filename in
      { Ast.file_name = filename; digest = Digest.string (ds^digest); deps = []; ast = s.ast @ m.ast  }
    else parse_one_file digest filename
  else parse_one_file digest filename)

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
  Hashtbl.clear already_parsed;
  Warnings.init ();
  let token = Lexer.token C.versions in

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

  (* the declarations and the errors (most recent first) *)
  let rec loop declarations errors error_count =
    last_token_lexed := None; first_token_lexed_loc := None;
    (* an error: it is recorded, the rest of the declaration is skipped *)
    let recover (loc, msg) =
      if max_errors = 0 then raise (Parser_config.ParseError (loc, msg));
      skip ();
      let errors = (loc, msg) :: errors in
      match !last_token_lexed with
      | Some Tokens.EOF -> declarations, errors
      | _ -> loop declarations errors (error_count + 1) in
    if max_errors > 0 && error_count >= max_errors then
      (* nothing is dropped silently *)
      declarations,
      (to_loc lexbuf, Printf.sprintf "too many errors (limit %d): the rest was not parsed, the result is incomplete" max_errors) :: errors
    else
    match parse ~lexer Grammar.Incremental.one_decl lexbuf with
    | Some d -> loop (d :: declarations) errors error_count
    | None -> declarations, errors
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
    | exception Cannot_accumulate msg -> recover (declaration_loc (), msg) in
  let declarations, errors = loop [] [] 0 in
  let ast = List.rev declarations in
  let filename = let open Util.Loc in
    Printf.sprintf "%s:%d:%d" start_loc.source_name start_loc.source_stop lexbuf.Lexing.lex_curr_pos in
  let ws = Warnings.consume () in
  { Ast.file_name = filename; deps = []; digest; ast },
  List.rev_map make_error errors,
  ws

(* a file, with its .sig if it is a .mod (as parse_ref does) *)
let program ?max_errors file =
  Hashtbl.clear already_parsed;
  let filename = C.resolver ~unit:file () in
  let read f =
    let ic = open_in_bin f in
    Fun.protect ~finally:(fun () -> close_in ic) (fun () -> really_input_string ic (in_channel_length ic)) in
  let one f =
    let text = read f in
    let dest = cleanup_fname f in
    let p, errors, warnings = program_from ?max_errors ~loc:(Util.Loc.initial dest) ~digest:(Digest.string text) (Lexing.from_string text) in
    { p with Ast.file_name = f }, errors, warnings in
  if String.equal (Filename.extension filename) ".mod" then begin
    let sig_filename = Filename.chop_extension filename ^ ".sig" in
    if Sys.file_exists sig_filename then begin
      let s, es, ws = one sig_filename in
      let m, em, wm = one filename in
      { Ast.file_name = filename; digest = Digest.string (s.Ast.digest ^ m.Ast.digest); deps = []; ast = s.ast @ m.ast }, es @ em, ws @ wm
    end else one filename
  end else one filename


module Internal = struct
let infix_SYMB = Grammar.infix_SYMB
let prefix_SYMB = Grammar.prefix_SYMB
let postfix_SYMB = Grammar.postfix_SYMB
end

end