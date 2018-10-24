(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* This module provides all the built-in predicates and evaluable constants. *)

open Elpi_API.Extend.BuiltInPredicate

(* Builtins that are part of the language, like "is" or "!" *)
val core_builtins : declaration list
(* Basic I/O facilities *)
val io_builtins : declaration list
(* Builtins to be backward compatible with Teyjus, eg extra i/o predicates *)
val lp_builtins : declaration list
(* Elpi predicates like print *)
val elpi_builtins : declaration list
(* Elpi non-logical predicates like var, new_int ... *)
val elpi_nonlogical_builtins : declaration list

(* All the above, to be used as a sane default in Setup.init *)
val std_declarations : declaration list
val std_builtins : Elpi_API.Setup.builtins

(* Type descriptors for built-in predicates *)
val pair : 'a data -> 'b data -> ('a * 'b) data
val option : 'a data -> 'a option data
val bool : bool data

val in_stream  : (in_channel * string) data
val out_stream : (out_channel * string) data
