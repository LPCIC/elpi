(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_ast

type fixity = Infixl | Infixr | Infix | Prefix | Prefixr | Postfix | Postfixl

(* raises Not_found is the constant has no declared fixity *)
val min_precedence : int   (* minimal precedence in use *)
val lam_precedence : int   (* precedence of lambda abstraction *)
val appl_precedence : int  (* precedence of applications *)
val inf_precedence : int   (* greater than any used precedence *)
val list_element_prec : int
val precedence_of : Func.t -> fixity * int

type gramext = { fix : fixity; sym : string; prec : int }

(* Loads the basic grammar and sets the paths.
 * ~silent=true (default) does not print accumulated files *)
val init : ?silent:bool -> lp_syntax:gramext list -> paths:string list -> cwd:string -> unit -> unit

(* BUG: extending the grammar is imperative, cannot be undone *)
val parse_program : string list -> program
val parse_program_from_stream : char Stream.t -> program
val parse_goal : string -> goal
val parse_goal_from_stream : char Stream.t -> goal

val get_literal : string -> string

(* Standard lambda prolog syntax *)
val lp_gramext : gramext list
