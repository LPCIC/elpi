(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_parser
open Compiler_data

type type_abbrevs = (TypeAssignment.skema * Ast.Loc.t) F.Map.t
[@@deriving show]

type arities = Arity.t F.Map.t


val check_disjoint : type_abbrevs:ScopedTypeExpression.t F.Map.t -> kinds:arities -> unit
val check_type : type_abbrevs:type_abbrevs -> kinds:arities -> ScopedTypeExpression.t -> Symbol.t * Symbol.t option * TypingEnv.symbol_metadata

val check_types : type_abbrevs:type_abbrevs -> kinds:arities -> ScopeTypeExpressionUniqueList.t F.Map.t -> TypingEnv.t
  
type runtime_types
[@@deriving show]
val empty_runtime_types : runtime_types
val compile_for_runtime : TypingEnv.t -> runtime_types
val runtime_resolve : runtime_types -> F.t -> Symbol.t

type env_undeclared = (TypeAssignment.t * Symbol.t) F.Map.t
[@@deriving show]

val check :
  type_abbrevs:type_abbrevs ->
  kinds:arities ->
  types:TypingEnv.t ->
  unknown:env_undeclared ->
  is_rule:bool -> (* a rule or a term (eg query) *)
  ScopedTerm.t ->
  exp:TypeAssignment.t ->
  env_undeclared

val check_chr_rule :
  type_abbrevs:type_abbrevs ->
  kinds:arities ->
  types:TypingEnv.t ->
  unknown:env_undeclared ->
  ('a,ScopedTerm.t) Ast.Chr.t ->
    env_undeclared

val check_undeclared : unknown:env_undeclared -> TypingEnv.t

val check_pred_name : types:TypingEnv.t -> loc:Elpi_util.Util.Loc.t -> F.t -> Symbol.t
val unknown_type_assignment : string -> TypeAssignment.t
