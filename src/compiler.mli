(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Util
open Data

type flags = {
  defined_variables : StrSet.t;
  allow_untyped_builtin : bool;
  print_passes : bool; (* debug *)
}
val default_flags : flags

type program
type 'a query

(* Flags are threaded *)
val program_of_ast : flags:flags -> Ast.Program.t -> program
val query_of_ast : program -> Ast.Goal.t -> unit query
val query_of_term :
  program -> (depth:int -> State.t -> State.t * (Loc.t * term)) -> unit query
val query_of_data :
  program -> Loc.t -> 'a Query.t -> 'a query

val pp_query : (depth:int -> Format.formatter -> term -> unit) -> Format.formatter -> 'a query -> unit

val executable_of_query : 'a query -> 'a executable

val term_of_ast : depth:int -> Loc.t * Ast.Term.t -> term

type quotation = depth:int -> State.t -> Loc.t -> string -> State.t * term
val set_default_quotation : quotation -> unit
val register_named_quotation : name:string -> quotation -> unit

val lp : quotation

val is_Arg : State.t -> term -> bool
val get_Args : State.t -> term StrMap.t
val mk_Arg : 
  State.t -> name:string -> args:term list ->
    State.t * term
val get_Arg : State.t -> name:string -> args:term list -> term

(* Quotes the program and the query, see elpi-quoted_syntax.elpi *)
val quote_syntax : 'a query -> term list * term

(* false means a type error was found *)
val static_check : Ast.Program.t -> (* header *)
  ?exec:(?max_steps:int -> unit executable -> unit outcome) ->
  ?checker:Ast.Program.t ->
  ?flags:flags ->
  'a query -> bool

val while_compiling : bool State.component
