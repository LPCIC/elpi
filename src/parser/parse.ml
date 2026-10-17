(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_lexer_config

exception ParseError = Parser_config.ParseError

module type Parser = sig
  val goal : loc:Util.Loc.t -> text:string -> Ast.Goal.t
  val goal_from : loc:Util.Loc.t -> Lexing.lexbuf -> Ast.Goal.t

  (* The parsing of programs is error resilient: it never fails. A declaration
     with a syntax error is skipped up to the next dot and dropped, and its
     error (component "Parser") is returned, in order, with the program.
     Parsing stops after [max_errors] errors (default: no limit), with a last
     error that says so. The lexbuf must hold the whole text. *)
  val program_from : ?max_errors:int -> loc:Util.Loc.t -> digest:Digest.t -> Lexing.lexbuf ->
    Ast.Program.t * Util.error list
  (* the same on a file (also with its .sig if the file is a .mod) *)
  val program : ?max_errors:int -> string -> Ast.Program.t * Util.error list
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
  

module ParseFile = struct
  let parse_file ?cwd file = !parse_ref ?cwd file
  let client_payload : Obj.t option ref = ref None
  let set_current_clent_loc_pyload x = client_payload := Some x
  let get_current_client_loc_payload () = !client_payload

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
    let ast =
      try parse Grammar.Incremental.program lexbuf
      with Failure msg when msg = "lexing: empty token" ->
        (* an unknown character, or the end of the file in a comment: an
           error in this file, not in the one that accumulates it *)
        let p = lexbuf.Lexing.lex_curr_p in
        let eof = lexbuf.Lexing.lex_eof_reached && lexbuf.Lexing.lex_curr_pos >= lexbuf.Lexing.lex_buffer_len in
        let loc = { Util.Loc.client_payload = None; source_name = p.pos_fname; line = p.pos_lnum;
                    line_starts_at = p.pos_bol; source_start = p.pos_cnum; source_stop = p.pos_cnum } in
        raise (Parser_config.ParseError (loc, if eof then "missing terminator for comment" else "unexpected character")) in
    let output = { Ast.file_name = filename; deps = []; digest; ast } in
    Hashtbl.add already_parsed digest output;
    output

let () =
  parse_ref := (fun ?cwd filename ->
  let filename = C.resolver ?cwd ~unit:filename () in
  let digest = Digest.file filename in
  if Filename.extension filename = ".mod" then
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

(* Error-resilient parsing: the program is parsed one declaration at a time.
   When a declaration has a syntax error, the tokens up to the next dot are
   skipped, the declaration is dropped from the AST, and its error is
   returned with the program. *)
let at_eof lexbuf = lexbuf.Lexing.lex_curr_pos >= lexbuf.Lexing.lex_buffer_len

(* skips the character that the lexer could not recognize *)
let skip_char lexbuf =
  let open Lexing in
  lexbuf.lex_curr_pos <- lexbuf.lex_curr_pos + 1;
  lexbuf.lex_start_pos <- lexbuf.lex_curr_pos;
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_cnum = lexbuf.lex_curr_p.pos_cnum + 1 };
  lexbuf.lex_start_p <- lexbuf.lex_curr_p

let program_from ?(max_errors = max_int) ~loc:start_loc ~digest lexbuf =
  Hashtbl.clear already_parsed;
  lexing_set_position lexbuf start_loc;
  let token = Lexer.token C.versions in
  let last = ref None in
  let first = ref None in (* the start of the declaration being parsed *)
  let lexer lexbuf =
    let t = token lexbuf in
    last := Some t;
    if !first = None then first := Some lexbuf.Lexing.lex_start_p;
    t in
  (* skips up to the next dot (or the end of the text); nothing to skip if the
     last token read is one of them *)
  let rec skip () =
    match !last with
    | Some (Tokens.FULLSTOP | Tokens.EOF) -> ()
    | _ ->
        let pos = lexbuf.Lexing.lex_curr_pos in
        match lexer lexbuf with
        | _ -> skip ()
        | exception (Lexer.Error _ | Failure _) ->
            (* the lexer must make progress, otherwise the character is skipped *)
            if lexbuf.Lexing.lex_curr_pos > pos then skip ()
            else if at_eof lexbuf then last := Some Tokens.EOF
            else (skip_char lexbuf; skip ()) in
  let errors = ref [] and count = ref 0 in
  let rec loop acc =
    last := None; first := None;
    if max_errors > 0 && !count >= max_errors then begin
      (* nothing is dropped silently *)
      errors := (to_loc lexbuf, Printf.sprintf "too many errors (limit %d): the rest was not parsed, the result is incomplete" max_errors) :: !errors;
      acc
    end else
    match parse ~lexer Grammar.Incremental.one_decl lexbuf with
    | Some d -> loop (d :: acc)
    | None -> acc
    | exception e ->
        (* the span of the declaration being parsed, up to where the error
           was found *)
        let declaration () =
          let loc = to_loc lexbuf in
          match !first with
          | Some p -> { loc with Util.Loc.source_start = p.pos_cnum; line = p.pos_lnum; line_starts_at = p.pos_bol }
          | None -> loc in
        let loc, msg = match e with
          | Parser_config.ParseError (loc, msg) when loc.Util.Loc.source_name <> start_loc.Util.Loc.source_name ->
              (* an error in an accumulated file: it is reported on the
                 accumulate directive, with the position in the file *)
              declaration (),
              Printf.sprintf "in %s, line %d, column %d: %s" loc.source_name loc.line
                (loc.source_start - loc.line_starts_at + 1) msg
          | Parser_config.ParseError (loc, msg) ->
              (* the error is reported just after the offending token, that
                 is the last one read: the error is made to cover it *)
              (if loc.Util.Loc.source_start = loc.source_stop
                  && loc.source_stop = lexbuf.Lexing.lex_curr_p.pos_cnum
               then to_loc lexbuf else loc), msg
          | Failure msg when msg = "lexing: empty token" ->
              (* an unknown character, or the end of the text in a comment *)
              if at_eof lexbuf then to_loc lexbuf, "missing terminator for comment"
              else begin
                (* the lexer did not consume the character *)
                let p = lexbuf.Lexing.lex_curr_p in
                let loc = { (to_loc lexbuf) with Util.Loc.source_start = p.pos_cnum; source_stop = p.pos_cnum + 1;
                                                 line = p.pos_lnum; line_starts_at = p.pos_bol } in
                skip_char lexbuf;
                loc, "unexpected character"
              end
          | Failure msg ->
              (* e.g. a file to accumulate that does not exist *)
              declaration (), msg
          | e -> raise e in
        (* with max_errors = 0 the first error is raised *)
        if max_errors = 0 then raise (Parser_config.ParseError (loc, msg));
        skip ();
        errors := (loc, msg) :: !errors; incr count;
        if !last = Some Tokens.EOF then acc else loop acc in
  let ast = List.rev (loop []) in
  let filename = let open Util.Loc in
    Printf.sprintf "%s:%d:%d" start_loc.source_name start_loc.source_stop lexbuf.Lexing.lex_curr_pos in
  { Ast.file_name = filename; deps = []; digest; ast },
  List.rev_map (fun (loc, message) -> { Util.component = "Parser"; loc = Some loc; message }) !errors

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
    let p, errors = program_from ?max_errors ~loc:(Util.Loc.initial dest) ~digest:(Digest.string text) (Lexing.from_string text) in
    { p with Ast.file_name = f }, errors in
  if Filename.extension filename = ".mod" then begin
    let sig_filename = Filename.chop_extension filename ^ ".sig" in
    if Sys.file_exists sig_filename then begin
      let s, es = one sig_filename in
      let m, em = one filename in
      { Ast.file_name = filename; digest = Digest.string (s.Ast.digest ^ m.Ast.digest); deps = []; ast = s.ast @ m.ast }, es @ em
    end else one filename
  end else one filename


module Internal = struct
let infix_SYMB = Grammar.infix_SYMB
let prefix_SYMB = Grammar.prefix_SYMB
let postfix_SYMB = Grammar.postfix_SYMB
end

end