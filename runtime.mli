(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Parser

module Utils :
 sig
  (* A regular error *)
  val error : string -> 'a

  (* An invariant is broken, i.e. a bug *)
  val anomaly : string -> 'a
  
  (* If we type check the program, then these are anomalies *)
  val type_error : string -> 'a
 end

type query
type program

val query_of_ast : int(* number of hidden constants *) -> term -> query
val program_of_ast : clause list -> int(* number of hidden constants*) * program
val execute_once : int(* number of hidden constants *) -> program -> query -> bool (* true means error *)
val execute_loop : int(* number of hidden constants *) -> program -> query -> unit
val pp_prolog : clause list -> unit

(* Extensions *)

type constant = int (* De Brujin levels *)
type term =
  (* Pure terms *)
  | Const of constant
  | Lam of term
  | App of constant * term * term list
  (* Clause terms: unif variables used in clauses *)
  | Arg of (*id:*)int * (*argsno:*)int
  | AppArg of (*id*)int * term list
  (* Heap terms: unif variables in the query *)
  | UVar of term oref * (*depth:*)int * (*argsno:*)int
  | AppUVar of term oref * (*depth:*)int * term list
  (* Misc: $custom predicates, ... *)
  | Custom of constant * term list
  | String of ASTFuncS.t
  | Int of int
  | Float of float
and 'a oref = {
  mutable contents : 'a;
(*   mutable rest : constraints *)
}
and constraints = exn list

val term_of_ast : depth:int -> Parser.term -> term

exception No_clause

module Pp :
 sig
  val uppterm :
    constant -> string list ->
    constant -> term array ->
      Format.formatter -> term -> unit
 end

module Constants :
 sig
  val funct_of_ast : ASTFuncS.t -> constant * term
  val string_of_constant : constant -> string

  val eqc : constant

  (* Value for unassigned UVar/Arg *)
  val dummy : term
 end

(* Custom predicates like $print. Must either raise No_clause or succeed
   with the list of new goals *)
val register_custom :
  string -> (depth:int -> env:term array -> term list -> term list) -> unit

(* Functions useful to implement custom predicates and evaluable functions *)

val deref : from:constant -> to_:constant -> int -> term -> term
val app_deref : from:constant -> to_:constant -> term list -> term -> term
