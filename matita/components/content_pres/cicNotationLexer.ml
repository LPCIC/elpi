(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

(* $Id: cicNotationLexer.ml 13249 2016-11-24 15:08:18Z fguidi $ *)

open Printf

exception Error of int * int * string

module StringSet = Set.Make(String)

(* Lexer *)
let regexp number = xml_digit+
let regexp utf8_blank = " " | "\r\n" | "\n" | "\t" | [160] (* this is a nbsp *)
let regexp percentage = 
  ('-' | "") [ '0' - '9' ] + '%'
let regexp floatwithunit = 
  ('-' | "") [ '0' - '9' ] + ["."] [ '0' - '9' ] + ([ 'a' - 'z' ] + | "" )
let regexp color = "#" [ '0' - '9' 'a' - 'f' 'A' - 'F' ] [ '0' - '9' 'a' - 'f'
'A' - 'F' ] [ '0' - '9' 'a' - 'f' 'A' - 'F' ] [ '0' - '9' 'a' - 'f' 'A' - 'F' ]
[ '0' - '9' 'a' - 'f' 'A' - 'F' ] [ '0' - '9' 'a' - 'f' 'A' - 'F' ]

  (* ZACK: breaks unicode's binder followed by an ascii letter without blank *)
(* let regexp ident_letter = xml_letter *)

let regexp ident_letter = [ 'a' - 'z' 'A' - 'Z' ]

  (* must be in sync with "is_ligature_char" below *)
let regexp ligature_char = [ "'`~!?@*()[]<>-+=|:;.,/\"" ]
let regexp ligature = ligature_char ligature_char+

let regexp we_proved = "we" utf8_blank+ "proved"
let regexp we_have = "we" utf8_blank+ "have"
let regexp let_rec = "let" utf8_blank+ "rec" 
let regexp let_corec = "let" utf8_blank+  "corec"
let regexp ident_decoration = '\'' | '?' | '`'
let regexp ident_cont = ident_letter | xml_digit | '_'
let regexp ident_start = ident_letter 
let regexp ident = ident_letter ident_cont* ident_decoration* 
let regexp variable_ident = '_' '_' number
let regexp pident = '_' ident

let regexp tex_token = '\\' ident

let regexp delim_begin = "\\["
let regexp delim_end = "\\]"

let regexp qkeyword = "'" ( ident | pident ) "'"

let regexp implicit = '?'
let regexp placeholder = '%'
let regexp meta = implicit number

let regexp csymbol = '\'' ident

let regexp begin_group = "@{" | "${"
let regexp end_group = '}'
let regexp wildcard = "$_"
let regexp ast_ident = "@" ident
let regexp ast_csymbol = "@" csymbol
let regexp meta_ident = "$" ident
let regexp meta_anonymous = "$_"
let regexp qstring = '"' [^ '"']* '"'

let regexp begincomment = "(**" utf8_blank
let regexp beginnote = "(*"
let regexp endcomment = "*)"
(* let regexp comment_char = [^'*'] | '*'[^')']
let regexp note = "|+" ([^'*'] | "**") comment_char* "+|" *)

let level1_layouts = 
  [ "sub"; "sup";
    "below"; "above";
    "over"; "atop"; "frac";
    "sqrt"; "root"; "mstyle" ; "mpadded"; "maction"

  ]

let level1_keywords =
  [ "hbox"; "hvbox"; "hovbox"; "vbox";
    "break";
    "list0"; "list1"; "sep";
    "opt";
    "term"; "ident"; "number";
  ] @ level1_layouts

let level2_meta_keywords =
  [ "if"; "then"; "elCicNotationParser.se";
    "fold"; "left"; "right"; "rec";
    "fail";
    "default";
    "anonymous"; "ident"; "number"; "term"; "fresh"
  ]

  (* (string, int) Hashtbl.t, with multiple bindings.
   * int is the unicode codepoint *)
let ligatures = Hashtbl.create 23

let _ =
  List.iter
    (fun (ligature, symbol) -> Hashtbl.add ligatures ligature symbol)
    [ ("->", <:unicode<to>>);   ("=>", <:unicode<Rightarrow>>);
      (":=", <:unicode<def>>);
    ]

let regexp uri_step = [ 'a' - 'z' 'A' - 'Z' '0' - '9' '_' '-' ''' ]+

let regexp uri =
  ("cic:/" | "theory:/")              (* schema *)
(*   ident ('/' ident)*                  |+ path +| *)
  uri_step ('/' uri_step)*            (* path *)
  ('.' ident)+                        (* ext *)
  ("#xpointer(" number ('/' number)+ ")")?  (* xpointer *)

let regexp nreference =
  "cic:/"                             (* schema *)
  uri_step ('/' uri_step)*            (* path *)
  '#'
  ( "dec"
  | "def" ":" number ""
  | "fix" ":" number ":" number ":" number
  | "cfx" ":" number
  | "ind" ":" number ":" number ":" number
  | "con" ":" number ":" number ":" number
  ) (* ext + reference *)

let error lexbuf msg =
  let begin_cnum, end_cnum = Ulexing.loc lexbuf in
  raise (Error (begin_cnum, end_cnum, msg))
let error_at_end lexbuf msg =
  let begin_cnum, end_cnum = Ulexing.loc lexbuf in
  raise (Error (begin_cnum, end_cnum, msg))

let return_with_loc token begin_cnum end_cnum =
  let flocation = HExtlib.floc_of_loc (begin_cnum,end_cnum) in
   token, flocation

let return lexbuf token =
  let begin_cnum, end_cnum = Ulexing.loc lexbuf in
    return_with_loc token begin_cnum end_cnum

let return_lexeme lexbuf name = return lexbuf (name, Ulexing.utf8_lexeme lexbuf)

let return_symbol lexbuf s = return lexbuf ("SYMBOL", s)
let return_eoi lexbuf = return lexbuf ("EOI", "")

let remove_quotes s = String.sub s 1 (String.length s - 2)

let mk_lexer token =
  let tok_func stream =
(*     let lexbuf = Ulexing.from_utf8_stream stream in *)
(** XXX Obj.magic rationale.
 * The problem.
 *  camlp5 constraints the tok_func field of Token.glexer to have type:
 *    Stream.t char -> (Stream.t 'te * flocation_function)
 *  In order to use ulex we have (in theory) to instantiate a new lexbuf each
 *  time a char Stream.t is passed, destroying the previous lexbuf which may
 *  have consumed a character from the old stream which is lost forever :-(
 * The "solution".
 *  Instead of passing to camlp5 a char Stream.t we pass a lexbuf, casting it to
 *  char Stream.t with Obj.magic where needed.
 *)
    let lexbuf = Obj.magic stream in
    Token.make_stream_and_location
      (fun () ->
        try
          token lexbuf
        with
        | Ulexing.Error -> error_at_end lexbuf "Unexpected character"
        | Ulexing.InvalidCodepoint p ->
            error_at_end lexbuf (sprintf "Invalid code point: %d" p))
  in
  {
    Token.tok_func = tok_func;
    Token.tok_using = (fun _ -> ());
    Token.tok_removing = (fun _ -> ()); 
    Token.tok_match = Token.default_match;
    Token.tok_text = Token.lexer_text;
    Token.tok_comm = None;
  }

let expand_macro lexbuf =
  let macro =
    Ulexing.utf8_sub_lexeme lexbuf 1 (Ulexing.lexeme_length lexbuf - 1)
  in
  try
    ("SYMBOL", Utf8Macro.expand macro)
  with Utf8Macro.Macro_not_found _ -> 
(* FG: unexpanded TeX macros are terminated by a space for rendering *)     
     "SYMBOL", (Ulexing.utf8_lexeme lexbuf ^ " ")

let remove_quotes s = String.sub s 1 (String.length s - 2)
let remove_left_quote s = String.sub s 1 (String.length s - 1)

let rec level2_pattern_token_group counter buffer =
  lexer
  | end_group -> 
      if (counter > 0) then
	Buffer.add_string buffer (Ulexing.utf8_lexeme lexbuf) ;
      snd (Ulexing.loc lexbuf)
  | begin_group -> 
      Buffer.add_string buffer (Ulexing.utf8_lexeme lexbuf) ;
      ignore (level2_pattern_token_group (counter + 1) buffer lexbuf) ;
      level2_pattern_token_group counter buffer lexbuf
  | _ -> 
      Buffer.add_string buffer (Ulexing.utf8_lexeme lexbuf) ;
      level2_pattern_token_group counter buffer lexbuf

let read_unparsed_group token_name lexbuf =
  let buffer = Buffer.create 16 in
  let begin_cnum, _ = Ulexing.loc lexbuf in
  let end_cnum = level2_pattern_token_group 0 buffer lexbuf in
    return_with_loc (token_name, Buffer.contents buffer) begin_cnum end_cnum

let handle_keywords lexbuf k name = 
  let s = Ulexing.utf8_lexeme lexbuf in
  if k s then
	    return lexbuf ("", s)
	  else
	    return lexbuf (name, s)
;;

let rec level2_meta_token =
  lexer
  | utf8_blank+ -> level2_meta_token lexbuf
  | ident ->
      handle_keywords lexbuf (fun x -> List.mem x level2_meta_keywords) "IDENT"
  | variable_ident -> return lexbuf ("IDENT", Ulexing.utf8_lexeme lexbuf)
  | pident ->
      handle_keywords lexbuf (fun x -> List.mem x level2_meta_keywords) "PIDENT"
  | "@{" -> read_unparsed_group "UNPARSED_AST" lexbuf
  | ast_ident ->
      return lexbuf ("UNPARSED_AST",
        remove_left_quote (Ulexing.utf8_lexeme lexbuf))
  | ast_csymbol ->
      return lexbuf ("UNPARSED_AST",
        remove_left_quote (Ulexing.utf8_lexeme lexbuf))
  | eof -> return_eoi lexbuf

let rec comment_token acc depth =
  lexer
  | beginnote ->
      let acc = acc ^ Ulexing.utf8_lexeme lexbuf in
      comment_token acc (depth + 1) lexbuf
  | endcomment ->
      let acc = acc ^ Ulexing.utf8_lexeme lexbuf in
      if depth = 0
      then acc
      else comment_token acc (depth - 1) lexbuf
  | _ ->
      let acc = acc ^ Ulexing.utf8_lexeme lexbuf in
      comment_token acc depth lexbuf

  (** @param k continuation to be invoked when no ligature has been found *)
let ligatures_token k =
  lexer
  | ligature ->
      let lexeme = Ulexing.utf8_lexeme lexbuf in
      (match List.rev (Hashtbl.find_all ligatures lexeme) with
      | [] -> (* ligature not found, rollback and try default lexer *)
          Ulexing.rollback lexbuf;
          k lexbuf
      | default_lig :: _ -> (* ligatures found, use the default one *)
          return_symbol lexbuf default_lig)
  | eof -> return_eoi lexbuf
  | _ ->  (* not a ligature, rollback and try default lexer *)
      Ulexing.rollback lexbuf;
      k lexbuf

let rec level2_ast_token status =
  lexer
  | let_rec -> return lexbuf ("LETREC","")
  | let_corec -> return lexbuf ("LETCOREC","")
  | we_proved -> return lexbuf ("WEPROVED","")
  | we_have -> return lexbuf ("WEHAVE","")
  | utf8_blank+ -> ligatures_token (level2_ast_token status) lexbuf
  | meta ->
     let s = Ulexing.utf8_lexeme lexbuf in
      return lexbuf ("META", String.sub s 1 (String.length s - 1))
  | implicit -> return lexbuf ("IMPLICIT", "")
  | placeholder -> return lexbuf ("PLACEHOLDER", "")
  | ident -> handle_keywords lexbuf (fun x -> StringSet.mem x status) "IDENT"
  | variable_ident -> return lexbuf ("IDENT", Ulexing.utf8_lexeme lexbuf)
  | pident -> handle_keywords lexbuf (fun x -> StringSet.mem x status) "PIDENT"
  | number -> return lexbuf ("NUMBER", Ulexing.utf8_lexeme lexbuf)
  | tex_token -> return lexbuf (expand_macro lexbuf)
  | nreference -> return lexbuf ("NREF", Ulexing.utf8_lexeme lexbuf)
  | uri -> return lexbuf ("URI", Ulexing.utf8_lexeme lexbuf)
  | qstring ->
      return lexbuf ("QSTRING", remove_quotes (Ulexing.utf8_lexeme lexbuf))
  | csymbol ->
      return lexbuf ("CSYMBOL", remove_left_quote (Ulexing.utf8_lexeme lexbuf))
  | "${" -> read_unparsed_group "UNPARSED_META" lexbuf
  | "@{" -> read_unparsed_group "UNPARSED_AST" lexbuf
  | '(' -> return lexbuf ("LPAREN", "")
  | ')' -> return lexbuf ("RPAREN", "")
  | meta_ident ->
      return lexbuf ("UNPARSED_META",
        remove_left_quote (Ulexing.utf8_lexeme lexbuf))
  | meta_anonymous -> return lexbuf ("UNPARSED_META", "anonymous")
  | beginnote -> 
      let _comment = comment_token (Ulexing.utf8_lexeme lexbuf) 0 lexbuf in
(*       let comment =
        Ulexing.utf8_sub_lexeme lexbuf 2 (Ulexing.lexeme_length lexbuf - 4)
      in
      return lexbuf ("NOTE", comment) *)
      ligatures_token (level2_ast_token status) lexbuf
  | begincomment -> return lexbuf ("BEGINCOMMENT","")
  | endcomment -> return lexbuf ("ENDCOMMENT","")
  | eof -> return_eoi lexbuf
  | _ -> return_symbol lexbuf (Ulexing.utf8_lexeme lexbuf)

and level1_pattern_token =
  lexer
  | utf8_blank+ -> ligatures_token level1_pattern_token lexbuf
  | number -> return lexbuf ("NUMBER", Ulexing.utf8_lexeme lexbuf)
  | ident ->handle_keywords lexbuf (fun x -> List.mem x level1_keywords) "IDENT"
  | variable_ident -> return lexbuf ("IDENT", Ulexing.utf8_lexeme lexbuf)
  | pident->handle_keywords lexbuf (fun x->List.mem x level1_keywords) "PIDENT" 
  | color -> return lexbuf ("COLOR", Ulexing.utf8_lexeme lexbuf)
  | percentage -> 
      return lexbuf ("PERCENTAGE", Ulexing.utf8_lexeme lexbuf)
  | floatwithunit -> 
      return lexbuf ("FLOATWITHUNIT", Ulexing.utf8_lexeme lexbuf)
  | tex_token -> return lexbuf (expand_macro lexbuf)
  | qkeyword ->
      return lexbuf ("QKEYWORD", remove_quotes (Ulexing.utf8_lexeme lexbuf))
  | '(' -> return lexbuf ("LPAREN", "")
  | ')' -> return lexbuf ("RPAREN", "")
  | eof -> return_eoi lexbuf
  | _ -> return_symbol lexbuf (Ulexing.utf8_lexeme lexbuf)

let level1_pattern_token = ligatures_token level1_pattern_token
let level2_ast_token status = ligatures_token (level2_ast_token status)

(* API implementation *)
type lexers = {
        level1_pattern_lexer : (string * string) Token.glexer;
        level2_ast_lexer : (string * string) Token.glexer;
        level2_meta_lexer : (string * string) Token.glexer
}

let mk_lexers keywords = 
  let initial_keywords = 
   [ "CProp"; "Prop"; "Type"; "Set"; "let"; "match";
   "with"; "in"; "and"; "to"; "as"; "on"; "return"; "done" ]
  in
  let status = 
    List.fold_right StringSet.add (initial_keywords @ keywords) StringSet.empty 
  in 
  {
        level1_pattern_lexer = mk_lexer level1_pattern_token;
        level2_ast_lexer = mk_lexer (level2_ast_token status);
        level2_meta_lexer = mk_lexer level2_meta_token
  }
;;
