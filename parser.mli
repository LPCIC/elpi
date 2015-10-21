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
  val andf2 : t
  val orf : t
  val implf : t
  val rimplf : t
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

type clause = term

type fixity = Infixl | Infixr | Infix | Prefix | Postfix

(* raises Not_found is the constant has no declared fixity *)
val precedence_of : ASTFuncS.t -> fixity * int
val parse_program : filenames:string list -> clause list
val parse_goal : string -> term
val parse_goal_from_stream : char Stream.t -> term
val get_literal : string -> string

module PointerFunc : sig
(* to avoid a cycle in the Makefile, we introduce a pointer 
   function which points to a function in the latex_exporter.ml *)
 val set_export_clauses : (clause list -> string) -> unit
 val flag : bool ref
end
