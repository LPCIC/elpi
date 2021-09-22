{
    open Parser


    exception EndInput
}

(* Refer to:

   https://www.cs.uni-potsdam.de/wv/lehre/Material/Prolog/Eclipse-Doc/userman/node139.html
   http://www.amzi.com/manuals/amzi/pro/ref_terms.htm

   for a list of valid tokens *)

(* Character classes *)
let upper_case = ['A' - 'Z']
let underline = '_'
let lower_case = ['a' - 'z']
let digit = ['0' - '9']
let blank_space = [' ' '\t']
let end_of_line = '\n'
let line_comment = '%' [^ '\n'] *
let open_comment = "/*"
let close_comment = "*/"
let escape = '\\'

(* Groups of characters *)
let alphanumerical = upper_case | underline | lower_case | digit
let any_character = [' ' - '~']
let non_escape = any_character # ['\\']
let sign = ['+' '-']

(* Atoms *)
let atom = lower_case alphanumerical *

(* Variables *)
let variable = (upper_case | underline) alphanumerical *

rule token = parse
    (* Meta-characters *)
    | [' ' '\t' '\n']   { token lexbuf }
    | eof               { EOF }

    (* Comments *)
    | line_comment      { token lexbuf }
    | open_comment      { comments 1 lexbuf }
    | close_comment     { raise (Failure "unmatched closed comment") }

    (* Atoms *)
    | atom as a         { ATOM a }
    | "!"               { ATOM "!" }

    (* Variables *)
    | variable as v     { VAR v }

    (* Symbols *)
    | ":-"              { RULE      }
    | '.'               { PERIOD    }
    | '('               { LPAREN    }
    | ')'               { RPAREN    }
    | ','               { COMMA     }

and comments count = parse
    | open_comment      { comments (1 + count) lexbuf }
    | close_comment     { match count with
                          | 1 -> token lexbuf
                          | n -> comments (n - 1) lexbuf
                        }
    | eof               { raise (Failure "unmatched open comment") }
    | _                 { comments count lexbuf }

