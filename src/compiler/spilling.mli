(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

val main : type_abbrevs:Compiler_data.TypeAssignment.type_abbrevs -> types:Compiler_data.TypingEnv.t -> Compiler_data.ScopedTerm.t -> Compiler_data.ScopedTerm.t
