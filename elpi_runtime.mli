(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)


open Elpi_ast
open Elpi_parser

type query
type program

(* Interpreter API *)

val query_of_ast : program -> Elpi_ast.term -> query
val program_of_ast : ?print:[`Yes|`Raw] -> Elpi_ast.decl list -> program
val execute_once : print_constraints:bool -> program -> query -> bool (* true means error *)
val execute_loop : program -> query -> unit

(* Extension API *)
val cint: int Elpi_util.CData.cdata
val cfloat: float Elpi_util.CData.cdata
val cstring:  Elpi_ast.Func.t Elpi_util.CData.cdata
type idx
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
  | UVar of term_attributed_ref * (*depth:*)int * (*argsno:*)int
  | AppUVar of term_attributed_ref * (*depth:*)int * term list
  (* Misc: $custom predicates, ... *)
  | Custom of constant * term list
  | CData of Elpi_util.CData.t
  | Cons of term * term
  | Nil
and term_attributed_ref = {
  mutable contents : term;
  mutable rest : stuck_goal list;
}
and stuck_goal = {
  mutable blockers : term_attributed_ref list;
  kind : stuck_goal_kind;
}
and stuck_goal_kind

val term_of_ast : depth:int -> Elpi_ast.term -> term
val oref : term -> term_attributed_ref
val pp_term : Format.formatter -> term -> unit
val show_term : term -> string

exception No_clause

module Pp :
 sig
  val ppterm :
    constant -> string list ->
    constant -> term array ->
      Format.formatter -> term -> unit
  val uppterm :
    constant -> string list ->
    constant -> term array ->
      Format.formatter -> term -> unit
 end

module Constants :
 sig
  val funct_of_ast : Func.t -> constant * term
  val show : constant -> string

  val eqc : constant
  val orc : constant
  val andc : constant
  val andc2 : constant
  val rimplc : constant

  (* Value for unassigned UVar/Arg *)
  val dummy : term
 end


module CustomConstraints : sig
  type 'a constraint_type

  (* Must be purely functional *)
  val declare_constraint :
    name:string ->
    pp:(Format.formatter -> 'a -> unit) ->
    empty:'a ->
      'a constraint_type

  (* may raise No_clause *)
  val update : 'a constraint_type -> ('a -> 'a) -> unit
  val read : 'a constraint_type -> 'a
end


(* Custom predicates like $print. Must either raise No_clause or succeed
   with the list of new goals *)
val register_custom :
  string ->
  (depth:int -> env:term array -> idx -> term list -> term list) ->
  unit

(* Functions useful to implement custom predicates and evaluable functions *)
val deref_uv : ?avoid:term_attributed_ref -> from:constant -> to_:constant -> int -> term -> term
val deref_appuv : ?avoid:term_attributed_ref -> from:constant -> to_:constant -> term list -> term -> term
val is_flex : term -> term_attributed_ref option
val print_delayed : unit -> unit
val delay_goal : depth:int -> idx -> goal:term -> on:term_attributed_ref list -> unit
val declare_constraint : depth:int -> idx -> goal:term -> on:term_attributed_ref list -> unit

val lp_list_to_list : term -> term list

val query_of_ast_cmap :
  int ->
  term Func.Map.t ->
  Elpi_ast.term -> string list * int * term array * term
val split_conj : term -> term list

val enable_typechecking : unit -> unit

val llam_unify : int -> term array -> int -> term -> term -> bool
