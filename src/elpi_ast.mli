(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module Ploc : sig
  include module type of struct include Ploc end
  val pp : Format.formatter -> t -> unit
  val show : t -> string
end

(* Prolog functors *)
module Func : sig
  type t
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val equal : t -> t -> bool
  val truef : t
  val andf : t
  val andf2 : t
  val orf : t
  val implf : t
  val rimplf : t
  val cutf : t
  val pif : t
  val sigmaf : t
  val eqf : t
  val isf : t
  val nilf : t
  val consf : t
  val letf : t
  val arrowf : t
  val sequentf : t
  val ctypef : t

  val dummyname : t
  val spillf : t

  val from_string : string -> t

  module Map : Map.S with type key = t
end

type term =
   Const of Func.t
 | App of term * term list
 | Lam of Func.t * term
 | CData of Elpi_util.CData.t
 | Quoted of quote
and quote = { data : string; kind : string option }

val equal_term : term -> term -> bool
val pp_term : Format.formatter -> term -> unit
val show_term : term -> string


type clause = {
  loc : Ploc.t;
  id : string option;
  insert : ([ `Before | `After ] * string) option;
  body : term;
}
type sequent = { eigen : term; context : term; conclusion : term }
and chr_rule = {
  to_match : sequent list;
  to_remove : sequent list;
  alignment : Func.t list;
  guard : term option;
  new_goal : sequent option;
}
[@@deriving show, create]

val create_chr_rule :
  ?to_match: sequent list ->
  ?to_remove: sequent list ->
  ?alignment:Func.t list ->
  ?guard:term option ->
  ?new_goal: sequent option ->
  unit -> chr_rule

val pp_chr_rule : Format.formatter -> chr_rule -> unit
val show_chr_rule : chr_rule -> string

type decl =
   Clause of clause
 | Local of Func.t
 | Begin
 | End
 | Mode of (Func.t * bool list * (Func.t * (Func.t * Func.t) list) option) list
 | Constraint of Func.t list
 | Chr of chr_rule
 | Accumulated of decl list
 | Macro of Ploc.t * Func.t * term
 | Type of bool(*external?*) * Func.t * term

val mkLocal : string -> decl

type program = decl list

val pp_program : Format.formatter -> program -> unit
val show_program : program -> string

type goal = Ploc.t * term
exception NotInProlog of string

val mkApp : term list -> term
val mkCon : string -> term
val mkNil : term
val mkSeq : term list -> term
val mkQuoted : string -> term
val mkFreshUVar : unit -> term
val mkFreshName : unit -> term
val mkLam : string -> term -> term
val mkC : Elpi_util.CData.t -> term

open Elpi_util.CData

val cfloat : float cdata
val cint : int cdata
val cstring : string cdata
val cloc : (Ploc.t * string option) cdata

