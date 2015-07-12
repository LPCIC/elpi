module type ASTFuncT =
  sig
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
  end;;

module ASTFuncS : ASTFuncT

type term =
   Const of ASTFuncS.t
 | Custom of ASTFuncS.t
 | App of term * term list
 | Lam of ASTFuncS.t * term
 | String of ASTFuncS.t
 | Int of int 

val parse_program : filenames:string list -> (term * term) list
val parse_goal : string -> term
