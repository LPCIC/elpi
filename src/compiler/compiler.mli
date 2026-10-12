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
  max_errors: int; (* resilient passes stop after that many errors; default 0: the first error is raised *)
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

val pp_error : Format.formatter -> error -> unit          (* location:, newline, Component: message *)
val pp_error_message : Format.formatter -> error -> unit  (* Component: message *)
val show_error : error -> string

type program
val program_of_ast : flags:flags -> header:header -> Ast.Program.t -> program * error list * warning list

type scoped_program
val scoped_program_name : scoped_program -> string
val scoped_program_digest : scoped_program -> Digest.t
val scoped_program_deps : scoped_program -> Ast.dependencies
val scoped_of_builtins : flags:flags -> header:header -> ?calc:CalcHooks.descriptor -> declared_builtins -> scoped_program
val scoped_of_ast : flags:flags -> header:header -> ?calc:CalcHooks.descriptor -> Ast.Program.t -> scoped_program list * error list * warning list

type checked_compilation_unit
val pp_checked_compilation_unit : Format.formatter -> checked_compilation_unit -> unit
val checked_compilation_unit_name : checked_compilation_unit -> string
val checked_compilation_unit_digest : checked_compilation_unit -> Digest.t
val checked_compilation_unit_deps : checked_compilation_unit -> Ast.dependencies

type unchecked_compilation_unit
val empty_base : header:header -> program
val unit_of_scoped : flags:flags -> header:header -> scoped_program -> unchecked_compilation_unit * error list * warning list
val check_unit : flags:flags -> base:program -> unchecked_compilation_unit -> checked_compilation_unit * error list * warning list
val compile_unit : flags:flags -> header:header -> base:program -> scoped_program -> checked_compilation_unit * error list * warning list
val append_unit : flags:flags -> base:program -> checked_compilation_unit -> program * error list * warning list

type checked_compilation_unit_signature
val signature_of_checked_compilation_unit : checked_compilation_unit -> checked_compilation_unit_signature
val checked_compilation_unit_signature_name : checked_compilation_unit_signature -> string
val checked_compilation_unit_signature_digest : checked_compilation_unit_signature -> Digest.t

val append_unit_signature : flags:flags -> base:program -> checked_compilation_unit_signature -> program * error list * warning list

val map_compilation_unit : (Util.CData.t -> Util.CData.t) -> checked_compilation_unit -> checked_compilation_unit

type query
val query_of_ast : program -> Ast.Goal.t -> (State.t -> State.t) -> (query, error) result * warning list
val query_of_scoped_term : program -> (State.t -> State.t * Compiler_data.ScopedTerm.t) -> (query, error) result * warning list
val query_of_raw_term : program -> (State.t -> State.t * term * Conversion.extra_goals) -> (query, error) result * warning list

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
  val of_list : (Ast.Loc.t * 'a) list -> 'a t
  val find : Ast.Loc.t -> 'a t -> (Ast.Loc.t * 'a) list
  val fold_file : string -> (Ast.Loc.t -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

type type_
val pp_type_ : Format.formatter -> type_ -> unit

type origin = User | Builtin | Core | Undeclared
type cls = Predicate | Function | Data
type kind =
  | Term
  | Constant of cls * origin
  | Bound
  | Binder
  | Unification_variable
  | Discard
  | Literal of [ `Int | `Float | `String | `Other ]
  | Keyword
  | Type_constructor | Type_abbreviation | Type_variable | Type_keyword
  | Macro

type description =
  | Type of type_
  | Text of string

type info = {
  kind : kind;
  description : description option;
  defined : Ast.Loc.t option;
  declaration : bool;
  occurrences : Ast.Loc.t list;
}
val pp_info : Format.formatter -> info -> unit

val hover : scoped_program -> checked_compilation_unit -> info IntervalTree.t
