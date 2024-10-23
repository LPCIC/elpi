open Elpi_lexer_config
open Elpi_parser

type t = Tokens.token =
  | VDASH
  | USE_SIG
  | USEONLY
  | TYPEABBREV
  | TYPE
  | STRING of ( string )
  | SLASH
  | SIGMA
  | SIG
  | SHORTEN
  | RULE
  | RPAREN
  | REPLACE
  | REMOVE
  | RCURLY
  | RBRACKET
  | QUOTED of ( string )
  | QDASH
  | PRED
  | PIPE
  | PI
  | OR
  | NIL
  | NAMESPACE
  | NAME
  | MODULE
  | MOD
  | MINUSs
  | MINUSr
  | MINUSi
  | MINUS
  | MACRO
  | LPAREN
  | LOCALKIND
  | LOCAL
  | LCURLY
  | LBRACKET
  | KIND
  | IS
  | IO_COLON of (char)
  | IO of (char)
  | INTEGER of ( int )
  | INDEX
  | IMPORT
  | IFF
  | IF
  | FUNCTIONAL
  | FULLSTOP
  | FRESHUV
  | FLOAT of ( float )
  | FIXITY of (string)
  | FAMILY_TIMES of (string)
  | FAMILY_TILDE of (string)
  | FAMILY_TICK of (string)
  | FAMILY_SHARP of (string)
  | FAMILY_QMARK of (string)
  | FAMILY_PLUS of (string)
  | FAMILY_OR of (string)
  | FAMILY_MINUS of (string)
  | FAMILY_LT of (string)
  | FAMILY_GT of (string)
  | FAMILY_EXP of (string)
  | FAMILY_EQ of (string)
  | FAMILY_BTICK of (string)
  | FAMILY_AND of (string)
  | EXTERNAL
  | EXPORTDEF
  | EQ2
  | EQ
  | EOF
  | DIV
  | DARROW
  | CUT
  | CONSTRAINT
  | CONSTANT of ( string )
  | CONS
  | CONJ2
  | CONJ
  | COLON
  | CLOSED
  | BIND
  | BEFORE
  | AS
  | ARROW
  | AFTER
  | ACCUM_SIG
  | ACCUMULATE
[@@deriving show]

let error s n msg =
  Printf.eprintf "lexing '%s' at char %d: %s\n" s n msg;
  exit 1

let validate s (tok1,lnum1,bol1,cnum1) (tok2,lnum2, bol2, cnum2) =
  if tok1 <> tok2 then error s cnum2   (Printf.sprintf "wrong token: got %s instead of %s" (show tok2) (show tok1));
  if lnum1 <> lnum2 then error s cnum2 (Printf.sprintf "wrong line number: got %d instead of %d" lnum2 lnum1);
  if bol1 <> bol2 then error s cnum2   (Printf.sprintf "wrong begin of line: got %d instead of %d" bol2 bol1);
  if cnum1 <> cnum2 then error s cnum2 (Printf.sprintf "wrong char count: got %d instead of %d" cnum2 cnum1)

type exp = T of t * int * int * int | E

let rec expect s b = function
  | [] -> ()
  | sp :: spec ->
      begin try
      let tok2 = Lexer.token b in
      let open Lexing in
      let p = b.lex_curr_p in
      let lnum2, bol2, cnum2 = p.pos_lnum, p.pos_bol, p.pos_cnum in
      match sp with
        | T (tok1,lnum1,bol1,cnum1) -> validate s (tok1,lnum1,bol1,cnum1) (tok2,lnum2, bol2, cnum2)
        | E -> error s cnum2 (Printf.sprintf "wrong lexing: got %s instead of error" (show tok2))
      with Failure _ ->
        match sp with
        | E -> ()
        | T (tok1,_,_,cnum1) -> error s cnum1 (Printf.sprintf "wrong lexing: got error instead of %s" (show tok1))
      end;
      expect s b spec

let test s spec =
  let s = Str.global_replace (Str.regexp_string "\r") "" s in
  let b = Lexing.from_string s in
  expect s b spec

let () =
  (*    01234567890123456789012345 *)
  test  "3.4"                        [T(FLOAT 3.4, 1, 0, 3)];
  test  " 3.4"                       [T(FLOAT 3.4, 1, 0, 4)];
  test  "\n3.4"                      [T(FLOAT 3.4, 2, 1, 4)];
  test  "3.4 .5"                     [T(FLOAT 3.4, 1, 0, 3); T(FLOAT 0.5, 1, 0, 6)];
  test  "3.4\n .5"                   [T(FLOAT 3.4, 1, 0, 3); T(FLOAT 0.5, 2, 4, 7)];
  (*    01234567890123456789012345 *)
  test  "3 .4"                       [T(INTEGER 3, 1, 0, 1); T(FLOAT 0.4, 1, 0, 4)];
  test  "3..4"                       [T(INTEGER 3, 1, 0, 1); T(FULLSTOP, 1, 0, 2); T(FLOAT 0.4, 1, 0, 4)];
  test  "3."                         [T(INTEGER 3, 1, 0, 1); T(FULLSTOP, 1, 0, 2)];
  test  "-3."                        [T(INTEGER (-3), 1, 0, 2); T(FULLSTOP, 1, 0, 3)];
  (*    01234567890123456789012345 *)
  test  "3%...\n3"                   [T(INTEGER 3, 1, 0, 1); T(INTEGER 3, 2, 6, 7)];
  test  "3/*..*/3"                   [T(INTEGER 3, 1, 0, 1); T(INTEGER 3, 1, 0, 8)];
  test  "3/** T **/3"                [T(INTEGER 3, 1, 0, 1); T(INTEGER 3, 1, 0, 11)];
  test  "3/*\n.*/3"                  [T(INTEGER 3, 1, 0, 1); T(INTEGER 3, 2, 4, 8)];
  test  "3/*\n/*\n*/*/3"             [T(INTEGER 3, 1, 0, 1); T(INTEGER 3, 3, 7, 12)];
  test  "3/*"                        [T(INTEGER 3, 1, 0, 1); E];
  (*    01234567890123456789012345 *)
  test {|"a"|}                        [T(STRING "a", 1, 0, 3)];
  test {|"a""b"|}                     [T(STRING "a\"b", 1, 0, 6)];
  test {|"a\nb"|}                     [T(STRING "a\nb", 1, 0, 6)];
  test {|"a
b"|}                                  [T(STRING "a\nb", 2, 3, 5)];
  (*    01234567890123456789012345 *)
  test  "x"                           [T(CONSTANT "x", 1, 0, 1)];
  test  "x-y"                         [T(CONSTANT "x-y", 1, 0, 3)];
  test  "-y"                          [T(MINUS, 1, 0, 1); T(CONSTANT "y",1,0,2)];
  test  "_y"                          [T(CONSTANT "_y", 1, 0, 2)];
  test  "_X"                          [T(CONSTANT "_X", 1, 0, 2)];
  test  "X_"                          [T(CONSTANT "X_", 1, 0, 2)];
  test  "x?"                          [T(CONSTANT "x?", 1, 0, 2)];
  test  "X"                           [T(CONSTANT "X", 1, 0, 1)];
  test  "X1>@!"                       [T(CONSTANT "X1>@!", 1, 0, 5)];
  test  "a.B.c"                       [T(CONSTANT "a.B.c", 1, 0, 5)];
  test  "a.B."                        [T(CONSTANT "a.B", 1, 0, 3); T(FULLSTOP, 1, 0, 4)];
  test  "a.>"                         [T(CONSTANT "a", 1, 0, 1); T(FULLSTOP, 1, 0, 2); T(FAMILY_GT ">", 1, 0, 3)];
  (*    01234567890123456789012345 *)
  test  "-->"                         [T(FAMILY_MINUS "-->", 1, 0, 3)];
  test  "x.y->z"                      [T(CONSTANT "x.y->z", 1, 0, 6)];
  (*    01234567890123456789012345 *)
  test  "{{{ }} }}}"                  [T(QUOTED " }} ", 1, 0, 10)];
  test  "{{ {{ } }} }}"               [T(QUOTED " {{ } }} ", 1, 0, 13)];
  test  "{{ x }}3"                    [T(QUOTED " x ", 1, 0, 7); T(INTEGER 3, 1, 0, 8)];
  test  "{{{ x }}}3"                  [T(QUOTED " x ", 1, 0, 9); T(INTEGER 3, 1, 0, 10)];
  test  "{{\n x }}3"                  [T(QUOTED "\n x ", 2, 4, 8); T(INTEGER 3, 2, 4, 9)];
  (*    01234567890123456789012345 *)
  test  "foo :- bar."                 [T(CONSTANT "foo", 1, 0, 3); T(VDASH, 1, 0, 6); T(CONSTANT "bar", 1, 0, 10); T(FULLSTOP, 1, 0, 11)];
  test  "foo ?- bar."                 [T(CONSTANT "foo", 1, 0, 3); T(QDASH, 1, 0, 6); T(CONSTANT "bar", 1, 0, 10); T(FULLSTOP, 1, 0, 11)];
  test  "foo :- x \\ bar."            [T(CONSTANT "foo", 1, 0, 3); T(VDASH, 1, 0, 6); T(CONSTANT "x", 1, 0, 8); T(BIND, 1, 0, 10); T(CONSTANT "bar", 1, 0, 14); T(FULLSTOP, 1, 0, 15)];
  test  "foo, bar"                    [T(CONSTANT "foo", 1, 0, 3); T(CONJ, 1, 0, 4); T(CONSTANT "bar", 1, 0, 8) ];
  test  "foo & bar"                    [T(CONSTANT "foo", 1, 0, 3); T(CONJ2, 1, 0, 5); T(CONSTANT "bar", 1, 0, 9) ];
  test  "[]"                          [T(LBRACKET, 1, 0, 1); T(RBRACKET, 1, 0, 2)];
  (*    01234567890123456789012345 *)
  test  "X"                           [T(CONSTANT "X", 1, 0, 1) ];
  test  "is"                          [T(IS, 1, 0, 2) ];
  test  "#line 3 \"xx\"\na"           [T(CONSTANT "a", 3, 0, 1) ];
  test  "b\n#line 3 \"xx\"\na"        [T(CONSTANT "b", 1, 0, 1);T(CONSTANT "a", 3, 2, 1) ];
  test  {|
b
c
#line 7 "xx"
a|}                                   [T(CONSTANT "b", 2, 1, 2);T(CONSTANT "c", 3, 3, 4);T(CONSTANT "a", 7, 5, 1) ];
  (*    01234567890123456789012345 *)
  test  ":name"                       [T(COLON,1,0,1); T(NAME,1,0,5)];
  test  "@foo"                        [T(CONSTANT "@foo",1,0,4)];
  test  "a && b"                       [T(CONSTANT "a",1,0,1);T(FAMILY_AND "&&",1,0,4);T(CONSTANT "b",1,0,6)];
  (*    01234567890123456789012345 *)
  test  "i:"                          [T(IO_COLON 'i', 1, 0, 2)];
  test  "o:"                          [T(IO_COLON 'o', 1, 0, 2)];
  test  "i :"                         [T(IO 'i', 1, 0, 1); T(COLON,1,0,3)];
  test  "o :"                         [T(IO 'o', 1, 0, 1); T(COLON,1,0,3)];
  test  "i"                           [T(IO 'i', 1, 0, 1)];
  test  "o"                           [T(IO 'o', 1, 0, 1)];
