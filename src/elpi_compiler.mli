(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_data

type flags = {
  defined_variables : StrSet.t;
  allow_untyped_builtin : bool;
}
val default_flags : flags

type program
type query

val program_of_ast : Elpi_ast.program -> program
val query_of_ast : program -> Elpi_ast.goal -> query
val query_of_term :
  program -> (depth:int -> CompilerState.t -> CompilerState.t * term) -> query

val pp_query : (depth:int -> Format.formatter -> term -> unit) -> Format.formatter -> query -> unit

val executable_of_query : ?flags:flags -> query -> executable

val term_of_ast : depth:int -> Elpi_ast.term -> term

type quotation = depth:int -> CompilerState.t -> string -> CompilerState.t * term
val set_default_quotation : quotation -> unit
val register_named_quotation : name:string -> quotation -> unit

val lp : quotation

val is_Arg : CompilerState.t -> term -> bool
val fresh_Arg : 
  CompilerState.t -> name_hint:string -> args:term list ->
    CompilerState.t * string * term

(* Quotes the program and the query, see elpi_quoted_syntax.elpi *)
val quote_syntax : query -> term list * term

(* false means a type error was found *)
val static_check : Elpi_ast.decl list -> (* header *)
  ?exec:(?max_steps:int -> executable -> outcome) ->
  ?checker:Elpi_ast.decl list ->
  ?flags:flags ->
  query -> bool
