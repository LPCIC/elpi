(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_parser
open Compiler_data

type type_abbrevs = (TypeAssignment.skema * Ast.Loc.t) F.Map.t
type arities = Arity.t F.Map.t

val check_disjoint : type_abbrevs:ScopedTypeExpression.t F.Map.t -> kinds:arities -> unit
val check_type : type_abbrevs:type_abbrevs -> kinds:arities -> ScopedTypeExpression.t -> Symbol.t * TypeAssignment.skema
val check_types : type_abbrevs:type_abbrevs -> kinds:arities -> TypeList.t -> (Symbol.t * TypeAssignment.skema) list * Symbol.t TypeAssignment.overloading F.Map.t

type typing_env = TypeAssignment.skema Symbol.QMap.t * Symbol.t TypeAssignment.overloading F.Map.t
type env_undeclared = (TypeAssignment.t * Scope.type_decl_id * Ast.Loc.t) F.Map.t
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
val unknown_type_assignment : string -> TypeAssignment.t
