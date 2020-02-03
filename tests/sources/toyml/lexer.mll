(* File lexer.mll *)
{
open Parser        (* The type token is defined in parser.mli *)
exception Eof
}
rule token = parse
    [' ' '\t' '\n']     { token lexbuf }     (* skip blanks *)
  | ['0'-'9']+ as lxm { INT(int_of_string lxm) }
  | "let"            { LET }
  | "in"           { IN }
  | "fun"           { LAM }
  | ['a'-'z']+ as lxm  { IDENT lxm }
  | '('            { LPAREN }
  | ')'            { RPAREN }
  | '['            { LBRK }
  | ']'            { RBRK }
  | '='            { EQ }
  | ','            { COMMA }
  | ';'            { SEMICOLON }
  | "->"            { ARROW }
  | eof            { EOF }
