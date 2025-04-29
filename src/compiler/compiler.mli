(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_parser
open Elpi_runtime

open Util
open Data

type flags = {
  defined_variables : StrSet.t;
  print_units : bool; (* debug *)
  time_typechecking : bool; (* bench type checker *)
  skip_det_checking: bool;
}
val default_flags : flags

type builtins = string * Data.BuiltInPredicate.declaration list

type header
val header_of_ast : flags:flags -> parser:(module Parse.Parser) -> State.descriptor -> Compiler_data.QuotationHooks.descriptor -> HoasHooks.descriptor -> CalcHooks.descriptor -> builtins list -> Ast.Program.t ->  header

type program
val program_of_ast : flags:flags -> header:header -> Ast.Program.t -> program

type scoped_program
val scoped_of_ast : flags:flags -> header:header -> Ast.Program.t -> scoped_program

type checked_compilation_unit
type unchecked_compilation_unit
val empty_base : header:header -> program
val unit_of_scoped : flags:flags -> header:header -> ?builtins:builtins list -> scoped_program -> unchecked_compilation_unit
val append_unit : flags:flags -> base:program -> checked_compilation_unit -> program
val check_unit : flags:flags -> base:program -> unchecked_compilation_unit -> checked_compilation_unit

type checked_compilation_unit_signature
val signature_of_checked_compilation_unit : checked_compilation_unit -> checked_compilation_unit_signature

val append_unit_signature : flags:flags -> base:program -> checked_compilation_unit_signature -> program

type query
val query_of_ast : program -> Ast.Goal.t -> (State.t -> State.t) -> query
val query_of_scoped_term : program -> (State.t -> State.t * Compiler_data.ScopedTerm.t) -> query
val query_of_raw_term : program -> (State.t -> State.t * term * Conversion.extra_goals) -> query

val total_type_checking_time : query -> float
val total_det_checking_time : query -> float

val optimize_query : query -> executable

val relocate_closed_term : from:symbol_table -> to_:program -> term -> (term, string) Stdlib.Result.t

val pp_program : (pp_ctx:pp_ctx -> depth:int -> Format.formatter -> term -> unit) -> Format.formatter -> program -> unit
val pp_goal : (pp_ctx:pp_ctx -> depth:int -> Format.formatter -> term -> unit) -> Format.formatter -> query -> unit

val elpi_language : Compiler_data.Scope.language
val elpi : Compiler_data.QuotationHooks.quotation

val uvk : uvar_body StrMap.t State.component
val pp_uvar_body : Format.formatter -> uvar_body -> unit
val pp_uvar_body_raw : Format.formatter -> uvar_body -> unit

val compile_term_to_raw_term :
  ?check:bool -> State.t -> program ->
  ?ctx:constant Compiler_data.Scope.Map.t ->
  depth:int -> Compiler_data.ScopedTerm.t -> State.t * term
val runtime_hack_term_to_raw_term :
  State.t -> program ->
  ?ctx:constant Compiler_data.Scope.Map.t ->
  depth:int -> Compiler_data.ScopedTerm.t -> term
val global_name_to_constant : State.t -> string -> constant