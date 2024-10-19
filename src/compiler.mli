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
val header_of_ast : flags:flags -> parser:(module Parse.Parser) -> State.descriptor -> Compiler_data.QuotationHooks.descriptor -> HoasHooks.descriptor -> CalcHooks.descriptor -> builtins list -> Ast.Program.t ->  header

type program
val program_of_ast : flags:flags -> header:header -> Ast.Program.t -> program

type checked_compilation_unit
type unchecked_compilation_unit
val empty_base : header:header -> program
val unit_of_ast : flags:flags -> header:header -> Ast.Program.t -> unchecked_compilation_unit
val append_unit : flags:flags -> base:program -> checked_compilation_unit -> program
val check_unit : base:program -> unchecked_compilation_unit -> checked_compilation_unit

type 'a query
val query_of_ast : program -> Ast.Goal.t -> (State.t -> State.t) -> unit query
val query_of_term :
  program -> (depth:int -> State.t -> State.t * (Loc.t * term) * Conversion.extra_goals) -> unit query
val query_of_data :
  program -> Loc.t -> 'a Query.t -> 'a query

val total_type_checking_time : 'a query -> float

val optimize_query : 'a query -> 'a executable

val term_of_ast : depth:int -> State.t -> string -> State.t * term
val relocate_closed_term : from:State.t -> to_:State.t -> term -> (term, string) Stdlib.Result.t

val pp_program : (pp_ctx:pp_ctx -> depth:int -> Format.formatter -> term -> unit) -> Format.formatter -> 'a query -> unit
val pp_goal : (pp_ctx:pp_ctx -> depth:int -> Format.formatter -> term -> unit) -> Format.formatter -> 'a query -> unit

val lookup_query_predicate : program -> string -> program * Data.constant

val lp : Compiler_data.QuotationHooks.quotation

val is_Arg : State.t -> term -> bool
val get_Args : State.t -> term StrMap.t
val mk_Arg :
  State.t -> name:string -> args:term list ->
    State.t * term
val get_Arg : State.t -> name:string -> args:term list -> term

(* Quotes the program and the query, see elpi-quoted_syntax.elpi *)
val quote_syntax : [ `Compiletime | `Runtime of constant -> term ] -> State.t -> 'a query -> State.t * term list * term

module CustomFunctorCompilation : sig

  val compile_singlequote : State.t -> F.t -> State.t * term
  val compile_backtick : State.t -> F.t -> State.t * term

  val is_singlequote : F.t -> bool
  val is_backtick : F.t -> bool

end
