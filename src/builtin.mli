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

(* Elpi/OCaml's runtime *)
val ocaml_runtime : declaration list

(** Easy export of OCaml's Map/Set modules, use as follows:
   module StrMap = API.Utils.Map.Make(String)
   ocaml_map ~name:"strmap" BuiltInData.string (module StrMap) *)
val ocaml_map :
  name:string ->
  'a API.Conversion.t -> (module API.Utils.Map.S with type key = 'a) ->
  declaration list
val ocaml_set :
  name:string ->
  'a API.Conversion.t -> (module API.Utils.Set.S with type elt = 'a and type t = 'b) ->
  declaration list
val ocaml_set_conv :
  name:string ->
  'a API.Conversion.t -> (module API.Utils.Set.S with type elt = 'a and type t = 'b) ->
  'b API.Conversion.t * declaration list
val int_set : API.Utils.IntSet.t API.Conversion.t
val string_set : API.Compile.StrSet.t API.Conversion.t
val loc_set : API.Utils.LocSet.t API.Conversion.t

(* All the above, to be used as a sane default in Setup.init *)
val std_declarations : declaration list
val std_builtins : API.Setup.builtins

(* Type descriptors for built-in predicates *)
val pair : 'a API.Conversion.t -> 'b API.Conversion.t -> ('a * 'b) API.Conversion.t
val triple : 'a API.Conversion.t -> 'b API.Conversion.t -> 'c API.Conversion.t -> ('a * 'b * 'c) API.Conversion.t
val quadruple : 'a API.Conversion.t -> 'b API.Conversion.t -> 'c API.Conversion.t -> 'd API.Conversion.t -> ('a * 'b * 'c * 'd) API.Conversion.t
val option : 'a API.Conversion.t -> 'a option API.Conversion.t
val bool : bool API.Conversion.t
val char : char API.Conversion.t

module PPX : sig
  val embed_option : 'a API.Conversion.embedding -> ('a option) API.Conversion.embedding
  val embed_pair : 'a API.Conversion.embedding -> 'b API.Conversion.embedding -> ('a * 'b) API.Conversion.embedding
  val embed_triple : 'a API.Conversion.embedding -> 'b API.Conversion.embedding -> 'c API.Conversion.embedding -> ('a * 'b * 'c) API.Conversion.embedding
  val embed_quadruple : 'a API.Conversion.embedding -> 'b API.Conversion.embedding -> 'c API.Conversion.embedding -> 'd API.Conversion.embedding -> ('a * 'b * 'c * 'd) API.Conversion.embedding
  val readback_option : 'a API.Conversion.readback -> ('a option) API.Conversion.readback
  val readback_pair : 'a API.Conversion.readback -> 'b API.Conversion.readback -> ('a * 'b) API.Conversion.readback
  val readback_triple : 'a API.Conversion.readback -> 'b API.Conversion.readback -> 'c API.Conversion.readback -> ('a * 'b * 'c) API.Conversion.readback
  val readback_quadruple : 'a API.Conversion.readback -> 'b API.Conversion.readback -> 'c API.Conversion.readback -> 'd API.Conversion.readback -> ('a * 'b * 'c * 'd) API.Conversion.readback
end

(* A standard way to make a predicate always succeed but still give errors *)
type diagnostic = private OK | ERROR of string API.BuiltInPredicate.ioarg
val diagnostic : diagnostic API.Conversion.t
val mkOK : diagnostic
val mkERROR : string -> diagnostic

(* A way to make an argument optional, _ of flex is mapped to Unspec *)
type 'a unspec = Given of 'a | Unspec
val unspec : 'a API.Conversion.t -> 'a unspec API.Conversion.t
val unspecC : ('a,'b,'c) API.ContextualConversion.t -> ('a unspec,'b,'c) API.ContextualConversion.t

(* The string is the "file name" *)
val in_stream  : (in_channel * string) API.Conversion.t
val out_stream : (out_channel * string) API.Conversion.t

(* This is the default checker [elpi-checker] *)
val default_checker : unit -> API.Compile.program
