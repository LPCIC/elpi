
(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_lexer_config

exception ParseError of Util.Loc.t * string

(* the name of a file in the locations of its contents (the parser removes
   the build directory of dune from it) *)
val cleanup_fname : string -> string

module type Parser = sig
  val goal : loc:Util.Loc.t -> text:string -> Ast.Goal.t
  val goal_from : loc:Util.Loc.t -> Lexing.lexbuf -> Ast.Goal.t

  (* A declaration with a syntax error is skipped up to the next dot and dropped.
     A syntax error in an accumulated file is located on the accumulate directive.
     Parsing stops after [max_errors] errors (default: no limit), with a last
     error that says so. *)
  val program_from : ?max_errors:int -> loc:Util.Loc.t -> digest:Digest.t -> Lexing.lexbuf ->
    Ast.Program.t * Util.error list * Util.warning list
  (* the same on a file (also with its .sig if the file is a .mod) *)
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

module Make(C : Config) : Parser_w_Internals
