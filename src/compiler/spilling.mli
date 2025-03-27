(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

val main : types:Type_checker.typing_env -> Compiler_data.ScopedTerm.t -> Compiler_data.ScopedTerm.t
