(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util

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

type attribute =
  Name of string | After of string | Before of string | If of string     

val pp_attribute :
    Format.formatter -> attribute -> unit
val show_attribute :
     attribute -> string

type ('term,'attributes) clause = {
  loc : Ploc.t;
  attributes : 'attributes;
  body : 'term;
}

val pp_clause :
  (Format.formatter -> 'term -> unit) ->
  (Format.formatter -> 'attribute -> unit) ->
    Format.formatter -> ('term,'attribute) clause -> unit
val show_clause :
  (Format.formatter -> 'term -> unit) ->
  (Format.formatter -> 'attribute -> unit) ->
     ('term,'attribute) clause -> string

type sequent = { eigen : term; context : term; conclusion : term }
and chr_rule = {
  to_match : sequent list;
  to_remove : sequent list;
  guard : term option;
  new_goal : sequent option;
}

val create_chr_rule :
  ?to_match: sequent list ->
  ?to_remove: sequent list ->
  ?guard: term ->
  ?new_goal: sequent ->
  unit -> chr_rule
val pp_chr_rule : Format.formatter -> chr_rule -> unit
val show_chr_rule : chr_rule -> string

type ('name,'term) macro = {
   mlocation : Ploc.t;
   maname : 'name;
   mbody : 'term
}

val pp_macro :
  (Format.formatter -> 'name -> unit) ->
  (Format.formatter -> 'term -> unit) ->
    Format.formatter -> ('name,'term) macro -> unit
val show_macro :
  (Format.formatter -> 'name -> unit) ->
  (Format.formatter -> 'term -> unit) ->
     ('name,'term) macro -> string

type tdecl = { textern : bool; tname : Func.t; tty : term }

val pp_tdecl :
    Format.formatter -> tdecl -> unit
val show_tdecl :
     tdecl -> string

type 'name mode =
  { mname : 'name; margs : bool list }

val pp_mode :
  (Format.formatter -> 'name -> unit) ->
    Format.formatter -> 'name mode -> unit
val show_mode :
  (Format.formatter -> 'name -> unit) ->
     'name mode -> string

type decl =
 (* Blocks *)
 | Begin of Ploc.t
 | Namespace of Ploc.t * Func.t
 | Constraint of Ploc.t * Func.t list
 | End of Ploc.t

 | Accumulated of decl list

 (* data *)
 | Clause of (term, attribute list) clause
 | Local of Func.t
 | Mode of Func.t mode list
 | Chr of chr_rule
 | Macro of (Func.t, term) macro
 | Type of tdecl

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

