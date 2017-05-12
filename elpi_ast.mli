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
  val sequentf : t
  val ctypef : t

  val dummyname : t
  val spillf : t

  val from_string : string -> t

  module Map : Map.S with type key = t
end

type term =
   Const of Func.t
 | Custom of Func.t
 | App of term * term list
 | Lam of Func.t * term
 | String of Func.t
 | Int of int 
 | Float of float 
 | Quoted of quote
and quote = { data : string; kind : string option }

val equal_term : term -> term -> bool
val compare_term : term -> term -> int
val pp_term : Format.formatter -> term -> unit
val show_term : term -> string


type clause = {
  loc : Ploc.t;
  id : string option;
  insert : ([ `Before | `After ] * string) option;
  body : term;
}
type 'func alignement =  'func list * [ `Spread | `Align ]
type ('term,'func_t) chr = {
  to_match : ('term * 'term) list;
  to_remove : ('term * 'term) list;
  alignement : 'func_t alignement;
  guard : 'term option;
  new_goal : 'term option;
  depth : int; (* not parsed *)
  nargs : int; (* not parsed *)
}

val create_chr :
  ?to_match:('a * 'a) list ->
  ?to_remove:('a * 'a) list ->
  ?alignement:'b alignement ->
  ?guard:'a ->
  ?new_goal:'a -> ?depth:int -> ?nargs:int -> unit -> ('a, 'b) chr

val pp_chr : 
  (Format.formatter -> 'term -> unit) ->
  (Format.formatter -> 'func_t -> unit) ->
     Format.formatter -> ('term,'func_t) chr -> unit
val show_chr :
  (Format.formatter -> 'term -> unit) ->
  (Format.formatter -> 'func_t -> unit) ->
     ('term,'func_t) chr -> string

type decl =
   Clause of clause
 | Local of Func.t
 | Begin
 | End
 | Mode of (Func.t * bool list * (Func.t * (Func.t * Func.t) list) option) list
 | Constraint of Func.t list
 | Chr of (term, Func.t) chr
 | Accumulated of decl list
 | Macro of Func.t * term
 | Type of Func.t * term

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
val mkCustom : string -> term
val mkFloat : float -> term
val mkInt : int -> term
val mkString : string -> term
val mkQuoted : string -> term
val mkFreshUVar : unit -> term
val mkFreshName : unit -> term
val mkLam : string -> term -> term
