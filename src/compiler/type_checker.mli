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
  | External of Elpi_parser.Ast.Structured.provenance option
[@@deriving show, ord]

type symbol_metadata = {
  ty : TypeAssignment.skema;
  indexing : indexing;
}
[@@deriving show]

val check_disjoint : type_abbrevs:ScopedTypeExpression.t F.Map.t -> kinds:arities -> unit
val check_type : type_abbrevs:type_abbrevs -> kinds:arities -> ScopedTypeExpression.t -> Symbol.t * Symbol.t option * symbol_metadata

type typing_env = {
  symbols : symbol_metadata Symbol.QMap.t;
  overloading : Symbol.t TypeAssignment.overloaded F.Map.t;
}
[@@deriving show]

val empty_typing_env : typing_env

val check_types : type_abbrevs:type_abbrevs -> kinds:arities -> ScopeTypeExpressionUniqueList.t F.Map.t -> typing_env
  
type env_undeclared = (TypeAssignment.t * Symbol.t) F.Map.t
[@@deriving show]

val check :
  is_rule:bool -> (* a rule or a term (eg query) *)
  type_abbrevs:type_abbrevs ->
  kinds:arities ->
  types:typing_env ->
  unknown:env_undeclared ->
  ScopedTerm.t ->
  exp:TypeAssignment.t ->
  env_undeclared

val check_undeclared : unknown:env_undeclared -> typing_env

val check_pred_name : types:typing_env -> loc:Elpi_util.Util.Loc.t -> F.t -> Symbol.t
val unknown_type_assignment : string -> TypeAssignment.t
