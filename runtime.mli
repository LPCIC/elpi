(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Parser

type query
type program

val query_of_ast : term -> query
val program_of_ast : clause list -> program
val execute_once : program -> query -> bool  (* true means error *)
val execute_loop : program -> query -> unit
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

exception No_clause

(* Custom predicates like $print, failure by raising No_clause *)
val register_custom :
  string -> (depth:int -> env:term array -> term list -> term list) -> unit

(* Evaluable functions for the "is" and related predicates *)
val register_eval :
  string -> (term list -> term) -> unit
