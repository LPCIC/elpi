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

type declared_builtins
val declare_builtins : file_name:string -> Data.BuiltInPredicate.declaration list -> declared_builtins
val declared_builtins_of_file : file_name:string -> declared_builtins
val file_of_declared_builtins : declared_builtins -> string
val document_fmt : Format.formatter -> calc:CalcHooks.descriptor -> declared_builtins -> unit
val document_file : ?header:string  -> calc:CalcHooks.descriptor -> file:string -> declared_builtins -> unit

type header
val header_of_ast : flags:flags -> parser:(module Parse.Parser) -> State.descriptor -> Compiler_data.QuotationHooks.descriptor -> HoasHooks.descriptor -> CalcHooks.descriptor -> declared_builtins list -> header

type program
val program_of_ast : flags:flags -> header:header -> Ast.Program.t -> program

type scoped_program
val scoped_of_ast : flags:flags -> header:header -> ?calc:CalcHooks.descriptor -> ?builtins:declared_builtins list -> Ast.Program.t -> scoped_program

type checked_compilation_unit
val pp_checked_compilation_unit : Format.formatter -> checked_compilation_unit -> unit
type unchecked_compilation_unit
val empty_base : header:header -> program
val unit_of_scoped : flags:flags -> header:header -> ?builtins:declared_builtins list -> scoped_program -> unchecked_compilation_unit
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

val uvk : uvar StrMap.t State.component
val pp_uvar_body : Format.formatter -> uvar -> unit
val pp_uvar_body_raw : Format.formatter -> uvar -> unit

val compile_term_to_raw_term :
  ?check:bool -> State.t -> program ->
  ?ctx:constant Compiler_data.Scope.Map.t ->
  depth:int -> Compiler_data.ScopedTerm.t -> State.t * term
val runtime_hack_term_to_raw_term :
  State.t -> program ->
  ?ctx:constant Compiler_data.Scope.Map.t ->
  depth:int -> Compiler_data.ScopedTerm.t -> term
val global_name_to_constant : State.t -> string -> constant

module IntervalTree : sig
  type 'a t
  val find : Ast.Loc.t -> 'a t -> (Ast.Loc.t * 'a) list
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

type type_
val pp_type_ : Format.formatter -> type_ -> unit

type info = { defined : Ast.Loc.t option; type_ : type_ option }
val pp_info : Format.formatter -> info -> unit

val hover : checked_compilation_unit -> info IntervalTree.t
