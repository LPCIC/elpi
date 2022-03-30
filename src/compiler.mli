(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_parser

open Util
open Data

type flags = {
  defined_variables : StrSet.t;
  print_passes : bool; (* debug *)
  print_units : bool; (* debug *)
}
val default_flags : flags

exception CompileError of Loc.t option * string

type builtins = string * Data.BuiltInPredicate.declaration list

type header
val header_of_ast : flags:flags -> parser:(module Parse.Parser) -> builtins list -> Ast.Program.t ->  header

type program
val program_of_ast : flags:flags -> header:header -> Ast.Program.t -> program

type compilation_unit
val unit_of_ast : flags:flags -> header:header -> Ast.Program.t -> compilation_unit
val assemble_units : flags:flags -> header:header -> compilation_unit list -> program
val append_units : flags:flags -> base:program -> compilation_unit list -> program

type 'a query
val query_of_ast : program -> Ast.Goal.t -> unit query
val query_of_term :
  program -> (depth:int -> State.t -> State.t * (Loc.t * term) * Conversion.extra_goals) -> unit query
val query_of_data :
  program -> Loc.t -> 'a Query.t -> 'a query

val optimize_query : 'a query -> 'a executable

val term_of_ast : depth:int -> State.t -> string -> State.t * term

val pp_query : (pp_ctx:pp_ctx -> depth:int -> Format.formatter -> term -> unit) -> Format.formatter -> 'a query -> unit

val lookup_query_predicate : program -> string -> program * Data.constant

type quotation = depth:int -> State.t -> Loc.t -> string -> State.t * term
val set_default_quotation : quotation -> unit
val register_named_quotation : name:string -> quotation -> unit

val lp : quotation

val is_Arg : State.t -> term -> bool
val get_Args : State.t -> term StrMap.t
val mk_Arg :
  State.t -> name:string -> args:term list ->
    State.t * term
val get_Arg : State.t -> name:string -> args:term list -> term

(* Quotes the program and the query, see elpi-quoted_syntax.elpi *)
val quote_syntax : [ `Compiletime | `Runtime of constant -> term ] -> State.t -> 'a query -> State.t * term list * term

(* false means a type error was found *)
val static_check :
  exec:(unit executable -> unit outcome) ->
  checker:program ->
  'a query -> bool

module CustomFunctorCompilation : sig

  val declare_singlequote_compilation : string -> (State.t -> F.t -> State.t * term) -> unit
  val declare_backtick_compilation : string -> (State.t -> F.t -> State.t * term) -> unit

  val compile_singlequote : State.t -> F.t -> State.t * term
  val compile_backtick : State.t -> F.t -> State.t * term

  val is_singlequote : F.t -> bool
  val is_backtick : F.t -> bool

end
