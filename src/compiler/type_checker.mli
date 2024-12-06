(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_parser
open Compiler_data

type type_abbrevs = (TypeAssignment.skema_w_id * Ast.Loc.t) F.Map.t
type arities = Arity.t F.Map.t

val check_disjoint : type_abbrevs:ScopedTypeExpression.t F.Map.t -> kinds:arities -> unit
val check_type : type_abbrevs:type_abbrevs -> kinds:arities -> ScopedTypeExpression.t -> TypeAssignment.skema_w_id
val check_types : type_abbrevs:type_abbrevs -> kinds:arities -> TypeList.t -> TypeAssignment.overloaded_skema_with_id

type env = TypeAssignment.overloaded_skema_with_id F.Map.t
type env_undeclared = (TypeAssignment.t * Scope.type_decl_id * Ast.Loc.t) F.Map.t
[@@deriving show]

val check :
  is_rule:bool -> (* a rule or a term (eg query) *)
  type_abbrevs:type_abbrevs ->
  kinds:arities ->
  types:env ->
  unknown:env_undeclared ->
  ScopedTerm.t ->
  exp:TypeAssignment.t ->
  env_undeclared

val check_undeclared : unknown:env_undeclared -> env
val unknown_type_assignment : string -> TypeAssignment.t
