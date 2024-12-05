(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_lexer_config

exception ParseError = Parser_config.ParseError

module type Parser = sig
  val program : file:string -> Ast.Program.decl list
  val goal : loc:Util.Loc.t -> text:string -> Ast.Goal.t
  
  val goal_from : loc:Util.Loc.t -> Lexing.lexbuf -> Ast.Goal.t
  val program_from : loc:Util.Loc.t -> Lexing.lexbuf -> Ast.Program.t
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
  val resolver : ?cwd:string -> unit:string -> unit -> string

end

module Make(C : Config) = struct
  
let parse_ref : (?cwd:string -> string -> Ast.Program.parser_output list) ref =
  ref (fun ?cwd:_ _ -> assert false)
  

module ParseFile = struct
  let parse_file ?cwd file = !parse_ref ?cwd file
  let client_payload : Obj.t option ref = ref None
  let set_current_clent_loc_pyload x = client_payload := Some x
  let get_current_client_loc_payload () = !client_payload

end

module Grammar = Grammar.Make(ParseFile)
  
let message_of_state s = try Error_messages.message s with Not_found -> "syntax error"
let chunk s (p1,p2) =
  String.sub s p1.Lexing.pos_cnum (p2.Lexing.pos_cnum - p1.Lexing.pos_cnum)

let parse grammar lexbuf =
  let buffer, lexer = MenhirLib.ErrorReports.wrap Lexer.token in
  try
    grammar lexer lexbuf
  with
  | Ast.Term.NotInProlog(loc,message) ->
      raise (Parser_config.ParseError(loc,message^"\n"))
  | Grammar.Error stateid ->
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

let already_parsed = Hashtbl.create 11

let () =
  parse_ref := (fun ?cwd filename ->
  let filename = C.resolver ?cwd ~unit:filename () in
  let dest = Re.Str.replace_first (Re.Str.regexp "/_build/[^/]+") "" filename in
  let digest = Digest.file filename in
  let to_parse =
    if Filename.extension filename = ".mod" then
      let sigf = Filename.chop_extension filename ^ ".sig" in
      if Sys.file_exists sigf then [sigf,Digest.file sigf;filename,digest]
      else [filename,digest]
    else [filename,digest] in
  to_parse |> List.map (fun (filename,digest) ->
    if Hashtbl.mem already_parsed digest then
      { Ast.Program.file_name = filename; digest; ast = [] }
    else
      let ic = open_in filename in
      let lexbuf = Lexing.from_channel ic in
      lexbuf.Lexing.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = dest };
      Hashtbl.add already_parsed digest true;
      let ast = parse Grammar.program lexbuf in
      close_in ic;
      { file_name = filename; digest; ast }))

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
  
let goal_from ~loc lexbuf =
  lexing_set_position lexbuf loc;
  parse Grammar.goal lexbuf
      
let goal ~loc ~text =
  let lexbuf = Lexing.from_string text in
  goal_from ~loc lexbuf

let program_from ~loc lexbuf =
  Hashtbl.clear already_parsed;
  lexing_set_position lexbuf loc;
  parse Grammar.program lexbuf

let program ~file =
  Hashtbl.clear already_parsed;
  List.(concat (map (fun { Ast.Program.ast = x } -> x) @@ !parse_ref file))

module Internal = struct
let infix_SYMB = Grammar.infix_SYMB
let prefix_SYMB = Grammar.prefix_SYMB
let postfix_SYMB = Grammar.postfix_SYMB
end

end