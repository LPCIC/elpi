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

(* TODO: to be moved elsewhere, obviously *)
module type Implementation =
 sig
  type query
  type program
  val query_of_ast : term -> query
  val program_of_ast : (term * term) list -> program
  val msg : query -> string
  val execute_once : program -> query -> bool  (* true means error *)
  val execute_loop : program -> query -> unit
  val pp_prolog : (term * term) list -> unit
 end
