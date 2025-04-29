(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Compiler_data
open Type_checker

(* returns if the clause is deterministic *)
val check_clause :
  type_abbrevs:type_abbrevs ->
  types:TypingEnv.t ->
  unknown:env_undeclared ->
    ScopedTerm.t -> unit
