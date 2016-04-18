(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

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

  val from_string : string -> t
end

type term =
   Const of Func.t
 | Custom of Func.t
 | App of term * term list
 | Lam of Func.t * term
 | String of Func.t
 | Int of int 
 | Float of float 

val equal_term : term -> term -> bool
val compare_term : term -> term -> int
val pp_term : Format.formatter -> term -> unit
val show_term : term -> string


type clause = term
type decl =
   Clause of clause
 | Local of Func.t
 | Begin
 | End
 | Mode of (Func.t * bool list * (Func.t * (Func.t * Func.t) list) option) list
 | Constraint of Func.t list
 | Accumulated of decl list

val mkLocal : string -> decl

type program = decl list
type goal = term
exception NotInProlog

val mkApp : term list -> term
val mkCon : string -> term
val mkNil : term
val mkSeq : term list -> term
val mkCustom : string -> term
val mkFloat : float -> term
val mkInt : int -> term
val mkString : string -> term
val mkFreshUVar : unit -> term
val mkFreshName : unit -> term
val mkLam : string -> term -> term
