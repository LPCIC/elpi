type pos = Lexing.position = {
  pos_fname : string;
  pos_lnum : int;
  pos_bol : int;
  pos_cnum : int;
}
[@@deriving show, ord, eq]
type position = pos * pos [@@deriving show, ord, eq]

type term =
 | Const of string (* global name  or  bound variable *)
 | Int of int      (* literals *)
 | App of ast * ast
 | Lam of string * ast
 | Let of string * ast * ast
 | Eq  of ast * ast
and ast = { loc : position; v : term }
[@@deriving show]

type tye =
 | Var of string
 | Integer
 | Boolean
 | Arrow of tye * tye
 | List of tye
 | Pair of tye * tye
[@@deriving show]

type quantification =
 | Any
 | EqualityType
[@@deriving show]

type typ =
 | All of string * quantification * typ
 | Mono of tye
[@@deriving show]
