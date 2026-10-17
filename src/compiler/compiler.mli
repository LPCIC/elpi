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

(* a pass returns its result and the errors found; it stops after
   flags.max_errors errors and records a final one saying so; with
   max_errors = 0 the first error is raised as CompileError *)
type error = Util.error = {
  component : string;  (* the pass that found the error, eg "Typechecker" *)
  loc : Ast.Loc.t option;
  message : string;    (* without the name of the component *)
}
val pp_error : Format.formatter -> error -> unit          (* location:, newline, Component: message *)
val pp_error_message : Format.formatter -> error -> unit  (* Component: message *)
val show_error : error -> string

type program
val program_of_ast : flags:flags -> header:header -> Ast.Program.t -> program * error list

type scoped_program
val scoped_program_name : scoped_program -> string
val scoped_program_digest : scoped_program -> Digest.t
val scoped_program_deps : scoped_program -> Ast.dependencies
val scoped_of_builtins : flags:flags -> header:header -> ?calc:CalcHooks.descriptor -> declared_builtins -> scoped_program
val scoped_of_ast : flags:flags -> header:header -> ?calc:CalcHooks.descriptor -> Ast.Program.t -> scoped_program list * error list

type checked_compilation_unit
val pp_checked_compilation_unit : Format.formatter -> checked_compilation_unit -> unit
val checked_compilation_unit_name : checked_compilation_unit -> string
val checked_compilation_unit_digest : checked_compilation_unit -> Digest.t
val checked_compilation_unit_deps : checked_compilation_unit -> Ast.dependencies

type unchecked_compilation_unit
val empty_base : header:header -> program
val unit_of_scoped : flags:flags -> header:header -> scoped_program -> unchecked_compilation_unit * error list
val check_unit : flags:flags -> base:program -> unchecked_compilation_unit -> checked_compilation_unit * error list
(* [unit_of_scoped] then [check_unit], with one budget of errors *)
val compile_unit : flags:flags -> header:header -> base:program -> scoped_program -> checked_compilation_unit * error list
val append_unit : flags:flags -> base:program -> checked_compilation_unit -> program * error list

type checked_compilation_unit_signature
val signature_of_checked_compilation_unit : checked_compilation_unit -> checked_compilation_unit_signature
val checked_compilation_unit_signature_name : checked_compilation_unit_signature -> string
val checked_compilation_unit_signature_digest : checked_compilation_unit_signature -> Digest.t

val append_unit_signature : flags:flags -> base:program -> checked_compilation_unit_signature -> program * error list

val map_compilation_unit : (Util.CData.t -> Util.CData.t) -> checked_compilation_unit -> checked_compilation_unit

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
  val of_list : (Ast.Loc.t * 'a) list -> 'a t
  val find : Ast.Loc.t -> 'a t -> (Ast.Loc.t * 'a) list
  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

type type_
val pp_type_ : Format.formatter -> type_ -> unit

type info = { defined : Ast.Loc.t option; type_ : type_ option }
val pp_info : Format.formatter -> info -> unit

(* hover information, as an interval tree: of the rules of a unit, with the
   type of each sub-expression and the declaration of its head; and of the type
   expressions of the declarations of a scoped program: location, text,
   location of the declaration of the type constructor. Both are cheaper than
   [iter_unit], that visits all the symbols. *)
val hover : checked_compilation_unit -> info IntervalTree.t
val hover_types : scoped_program -> (Ast.Loc.t * string * Ast.Loc.t option) list

type origin = User | Builtin | Core | Undeclared
type cls = Predicate | Function | Data
type kind =
  | Constant of cls * origin  (* a symbol resolved to a declaration *)
  | Bound                     (* occurrence of a variable bound by x\, pi x\, sigma x\ *)
  | Binder                    (* the binding occurrence of such a variable *)
  | Unification_variable      (* a variable of the rule *)
  | Discard
  | Literal of [ `Int | `Float | `String | `Other ]
  | Keyword                   (* :- => , ; ! pi sigma *)
  | Type_constructor | Type_abbreviation | Type_variable | Type_keyword
  | Macro                     (* a use of a macro, @name *)

type node = {
  loc : Ast.Loc.t;               (* of the name of the symbol *)
  kind : kind;
  name : string option;
  defined : Ast.Loc.t option;    (* the declaration of a constant, the binder (with
                                    pi/sigma, without the backslash) of a bound
                                    variable, the head of the rule of a unification variable,
                                    the declaration of a macro *)
  declaration : bool;            (* the binding occurrence of a variable, the symbol that a rule defines (the head of its head) *)
}
val pp_node : Format.formatter -> node -> unit

(* [iter_unit sp u f] calls [f] on the symbols of the unit [u]: of its rules,
   CHR rules and macros, and of the type expressions of the declarations of
   its scoped program [sp] *)
val iter_unit : scoped_program -> checked_compilation_unit -> (node -> unit) -> unit
