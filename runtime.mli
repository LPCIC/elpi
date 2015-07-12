(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Parser

type query
type program

val query_of_ast : term -> query
val program_of_ast : (term * term) list -> program
val execute_once : program -> query -> bool  (* true means error *)
val execute_loop : program -> query -> unit
val pp_prolog : (term * term) list -> unit

