(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_parser
open Compiler_data

type type_abbrevs = (TypeAssignment.skema * Ast.Loc.t) F.Map.t
[@@deriving show]

type arities = Arity.t F.Map.t

type indexing =
  | Index of Elpi_util.Util.Mode.hos * Elpi_runtime.Data.indexing
  | DontIndex
[@@deriving show]

val compatible_indexing : indexing -> indexing -> bool

type symbol_metadata = {
  ty : TypeAssignment.skema;
  indexing : indexing;
  availability : Elpi_parser.Ast.Structured.symbol_availability;
}
[@@deriving show]

val check_disjoint : type_abbrevs:ScopedTypeExpression.t F.Map.t -> kinds:arities -> unit
val check_type : type_abbrevs:type_abbrevs -> kinds:arities -> ScopedTypeExpression.t -> Symbol.t * Symbol.t option * symbol_metadata

type typing_env
[@@deriving show]

val empty_typing_env : typing_env

val resolve_name : F.t -> typing_env -> Symbol.t TypeAssignment.overloaded
val resolve_symbol : Symbol.t -> typing_env -> symbol_metadata
val merge_envs : typing_env -> typing_env -> typing_env

val iter_names : (F.t -> Symbol.t TypeAssignment.overloaded -> unit) -> typing_env -> unit
val iter_symbols : (Symbol.t -> symbol_metadata -> unit) -> typing_env -> unit

val same_symbol : typing_env -> Symbol.t -> Symbol.t -> bool
val undup : typing_env -> Symbol.t list -> Symbol.t list
val all_symbols : typing_env -> (Symbol.t * symbol_metadata) list
val mem_symbol : typing_env -> Symbol.t -> bool
val canon : typing_env -> Symbol.t -> Symbol.t

val check_types : type_abbrevs:type_abbrevs -> kinds:arities -> ScopeTypeExpressionUniqueList.t F.Map.t -> typing_env
  
type runtime_types
[@@deriving show]
val empty_runtime_types : runtime_types
val compile_for_runtime : typing_env -> runtime_types
val runtime_resolve : runtime_types -> F.t -> Symbol.t

type env_undeclared = (TypeAssignment.t * Symbol.t) F.Map.t
[@@deriving show]

val check :
  type_abbrevs:type_abbrevs ->
  kinds:arities ->
  types:typing_env ->
  unknown:env_undeclared ->
  is_rule:bool -> (* a rule or a term (eg query) *)
  ScopedTerm.t ->
  exp:TypeAssignment.t ->
  env_undeclared

val check_chr_rule :
  type_abbrevs:type_abbrevs ->
  kinds:arities ->
  types:typing_env ->
  unknown:env_undeclared ->
  ('a,ScopedTerm.t) Ast.Chr.t ->
    env_undeclared

val check_undeclared : unknown:env_undeclared -> typing_env

val check_pred_name : types:typing_env -> loc:Elpi_util.Util.Loc.t -> F.t -> Symbol.t
val unknown_type_assignment : string -> TypeAssignment.t

module Internal : sig
  val cast : Symbol.t TypeAssignment.overloaded F.Map.t * symbol_metadata Symbol.QMap.t -> typing_env
end