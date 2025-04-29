(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* extensible syntax *)
type fixity = Infixl | Infixr | Infix | Prefix | Postfix

let pp_fixity fmt = function
 | Infixl  -> Format.fprintf fmt "Infix   left  associative"
 | Infixr  -> Format.fprintf fmt "Infix   right associative"
 | Infix   -> Format.fprintf fmt "Infix   not   associative"
 | Prefix  -> Format.fprintf fmt "Prefix  not   associative"
 | Postfix -> Format.fprintf fmt "Postfix not   associative"

let fixity_of_string = function
 | "infixl" -> Infixl 
 | "infixr" -> Infixr 
 | "infix" -> Infix 
 | "prefix" -> Prefix 
 | "prefixr" -> Prefix
 | "postfix" -> Postfix 
 | "postfixl" -> Postfix
 | _ -> assert false

(* family of tokens *)

type extensible = {
  start : string;
  mk_token : string -> Tokens.token;
  token : string;
  non_enclosed : bool;
  at_least_one_char : bool;
  fixed : string list;
}

type fixed = {
  token : string;
  the_token : string;
  mk_token : Tokens.token;
  comment : (int * string) option;
}

type mixfix_kind = Fixed of fixed | Extensible of extensible

type mixfix = {
  tokens : mixfix_kind list;
  fixity : fixity;
}

let mkFix ?comment token the_token mk_token = Fixed { token; the_token; mk_token; comment }

let mkExt token start ?(non_enclosed=false) ?(at_least_one_char=false) ?(fixed=[]) mk_token =
  Extensible { start; mk_token; token; non_enclosed; at_least_one_char; fixed }

let comment = 1, "The LHS of ==> binds stronger than conjunction, hence (a,b ==> c,d) reads a, (b ==> (c,d))" 
let mixfix_symbols : mixfix list = [
  { tokens = [ mkFix "VDASH" ":-" VDASH;
               mkFix "QDASH" "?-" QDASH];
    fixity = Infix };
  { tokens = [ mkFix "OR" ";" OR];
    fixity = Infixr };
  { tokens = [ mkFix ~comment "DDARROW" "==>" DDARROW];
    fixity = Infixr };
  { tokens = [ mkFix ~comment "DDARROWBANG" "=!=>" DDARROWBANG];
    fixity = Infixr };
  { tokens = [ mkFix "CONJ" "," CONJ;
               mkFix "CONJ2" "&" CONJ2];
    fixity = Infixr };
  { tokens = [ mkFix "ARROW" "->" ARROW];
    fixity = Infixr };
  { tokens = [ mkFix "DARROW" "=>" DARROW];
    fixity = Infixr };
  { tokens = [ mkFix "EQ" "=" EQ;
               mkFix "EQ2" "==" EQ2;
               mkExt "FAMILY_LT" "<" ~fixed:["=<"; "r<"; "i<"; "s<"; "r=<"; "i=<"; "s=<"] (fun x -> FAMILY_LT x);
               mkExt "FAMILY_GT" ">" ~fixed:["r>"; "i>"; "s>"; "r>="; "i>="; "s>="] (fun x -> FAMILY_GT x);
               mkFix "IS" "is" IS;
               ];
    fixity = Infix};
  { tokens = [ mkFix "CONS" "::" CONS];
    fixity = Infixr};
  { tokens = [ mkExt "FAMILY_TICK" "'" ~non_enclosed:true (fun x -> FAMILY_TICK x) ];
    fixity = Infix};
  { tokens = [ mkExt "FAMILY_EXP" "^" (fun x -> FAMILY_EXP x);
               mkExt "FAMILY_PLUS" "+" ~fixed:["r+";"i+";"s+"] (fun x -> FAMILY_PLUS x);
               mkFix "MINUS" "-" MINUS;
               mkFix "MINUSr" "r-" MINUSr;
               mkFix "MINUSi" "i-" MINUSi;
               mkFix "MINUSs" "s-" MINUSs; ];
    fixity = Infixl};
  { tokens = [ mkExt "FAMILY_TIMES" "*" ~fixed:["r*";"i*";"s*"] (fun x -> FAMILY_TIMES x);
              mkFix "SLASH" "/" SLASH;
              mkFix "DIV" "div" DIV;
              mkFix "MOD" "mod" MOD; ];
    fixity = Infixl};
  { tokens = [ mkExt "FAMILY_MINUS" "--" (fun x -> FAMILY_MINUS x) ];
    fixity = Infixr};
  { tokens = [ mkExt "FAMILY_BTICK" "`" ~non_enclosed:true (fun x -> FAMILY_BTICK x) ];
    fixity = Infix};
  { tokens = [ mkExt "FAMILY_EQ" "==" ~at_least_one_char:true (fun x -> FAMILY_EQ x) ];
    fixity = Infixr};
  { tokens = [ mkExt "FAMILY_OR" "||" (fun x -> FAMILY_OR x) ];
    fixity = Infixr};
  { tokens = [ mkExt "FAMILY_AND" "&&" (fun x -> FAMILY_AND x) ];
    fixity = Infixr};
  { tokens = [ mkExt "FAMILY_SHARP" "#" (fun x -> FAMILY_SHARP x) ];
    fixity = Infixl};
  { tokens = [ mkExt "FAMILY_TILDE" "~" ~fixed:["r~"; "i~"] (fun x -> FAMILY_TILDE x) ];
    fixity = Prefix};
  { tokens = [ mkExt "FAMILY_QMARK" "?" (fun x -> FAMILY_QMARK x) ];
    fixity = Postfix};
]
;;

