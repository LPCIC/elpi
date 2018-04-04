(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* This module provides all the built-in predicates and evaluable constants. *)


open Elpi_API.Extend.BuiltInPredicate

(* Builtins to be backward compatible with Teyjus, eg i/o predicates *)
val lp_builtins : declaration list
(* Elpi predicates like print *)
val elpi_builtins : declaration list
(* Elpi non-logical predicates like var, new_int ... *)
val elpi_nonlogical_builtins : declaration list

(* All the above, to be used as a sane default in Setup.init *)
val std_builtins : Elpi_API.Setup.builtins

