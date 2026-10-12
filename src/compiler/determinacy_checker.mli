(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Compiler_data
open Type_checker

(* checks if the clause adheres to the prescribed determinacy *)
(* the warnings (flexible rules) are recorded in [errs] *)
val check_clause :
  errs:Errors.t ->
  type_abbrevs:type_abbrevs ->
  types:TypingEnv.t ->
  unknown:env_undeclared ->
    ScopedTerm.t -> unit

(* checks [guard, !, newgoal] is det *)
val check_chr_guard_and_newgoal :
  errs:Errors.t ->
  type_abbrevs:type_abbrevs ->
  types:TypingEnv.t ->
  unknown:env_undeclared ->
    guard:ScopedTerm.t option -> newgoal:ScopedTerm.t -> unit
