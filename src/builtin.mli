(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* This module provides all the built-in predicates and evaluable constants. *)

open API.BuiltIn

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

(* Elpi stdlib *)
val elpi_stdlib : declaration list

(* Elpi datastructures *)
val elpi_map : declaration list
val elpi_set : declaration list

(** Easy export of OCaml's Map/Set modules, use as follows:
   module StrMap = API.Utils.Map.Make(String)
   ocaml_map ~name:"strmap" BuiltInData.string (module StrMap) *)
val ocaml_map :
  name:string ->
  ('a, API.Conversion.ctx) API.Conversion.t -> (module API.Utils.Map.S with type key = 'a) ->
  declaration list
val ocaml_set :
  name:string ->
  ('a, API.Conversion.ctx) API.Conversion.t -> (module API.Utils.Set.S with type elt = 'a) ->
  declaration list

(* All the above, to be used as a sane default in Setup.init *)
val std_declarations : declaration list
val std_builtins : API.Setup.builtins

(* Type descriptors for built-in predicates *)
val pair : ('a,'c) API.Conversion.t -> ('b,'c) API.Conversion.t -> ('a * 'b, 'c) API.Conversion.t
val option : ('a,'c) API.Conversion.t -> ('a option,'c) API.Conversion.t

val triple    : ('a, 'h) API.Conversion.t -> ('b, 'h) API.Conversion.t -> ('c, 'h) API.Conversion.t -> ('a * 'b * 'c, 'h) API.Conversion.t
val quadruple : ('a, 'h) API.Conversion.t -> ('b, 'h) API.Conversion.t -> ('c, 'h) API.Conversion.t -> ('d, 'h) API.Conversion.t -> ('a * 'b * 'c * 'd, 'h) API.Conversion.t
val quintuple : ('a, 'h) API.Conversion.t -> ('b, 'h) API.Conversion.t -> ('c, 'h) API.Conversion.t -> ('d, 'h) API.Conversion.t -> ('e, 'h) API.Conversion.t -> ('a * 'b * 'c * 'd * 'e, 'h) API.Conversion.t

(* This is the default checker [elpi-checker] *)
val default_checker : unit -> API.Compile.program
