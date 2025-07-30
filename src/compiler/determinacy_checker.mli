(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Compiler_data
open Type_checker

(* checks if the clause adheres to the prescribed determinacy *)
val check_clause :
  type_abbrevs:type_abbrevs ->
  types:TypingEnv.t ->
  unknown:env_undeclared ->
    ScopedTerm.t -> unit

(* checks the atoms are det *)
val check_atoms :
  type_abbrevs:type_abbrevs ->
  types:TypingEnv.t ->
  unknown:env_undeclared ->
    ScopedTerm.t list -> unit
