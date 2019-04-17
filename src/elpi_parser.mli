(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
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
val init : lp_syntax:gramext list -> paths:string list -> cwd:string ->
  unit -> unit

(* BUG: extending the grammar is imperative, cannot be undone *)
val parse_program : print_accumulated_files:bool -> string list -> Program.t
val parse_program_from_stream : print_accumulated_files:bool -> Loc.t -> char Stream.t -> Program.t
val parse_goal : ?loc:Loc.t -> string -> Goal.t
val parse_goal_from_stream : ?loc:Loc.t -> char Stream.t -> Goal.t

exception ParseError of Loc.t * string

val get_literal : string -> string

(* Standard lambda prolog syntax *)
val lp_gramext : gramext list
