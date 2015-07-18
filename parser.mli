(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

(* Prolog functors *)
module ASTFuncS : sig
  type t
  val compare : t -> t -> int
  val pp : t -> string
  val eq : t -> t -> bool
  val truef : t
  val andf : t
  val orf : t
  val implf : t
  val cutf : t
  val pif : t
  val sigmaf : t
  val eqf : t
  val isf : t
  val from_string : string -> t
end

type term =
   Const of ASTFuncS.t
 | Custom of ASTFuncS.t
 | App of term * term list
 | Lam of ASTFuncS.t * term
 | String of ASTFuncS.t
 | Int of int 
 | Float of float 

type clause = { head : term; hyps : term }

val parse_program : filenames:string list -> clause list
val parse_goal : string -> term
