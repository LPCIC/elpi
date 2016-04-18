(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)


open Elpi_ast
open Elpi_parser

module Utils :
 sig
  (* A regular error *)
  val error : string -> 'a

  (* An invariant is broken, i.e. a bug *)
  val anomaly : string -> 'a
  
  (* If we type check the program, then these are anomalies *)
  val type_error : string -> 'a

  val pplist : ?max:int -> ?boxed:bool ->
    (Format.formatter -> 'a -> unit) ->
    ?pplastelem:(Format.formatter -> 'a -> unit) ->
      string -> Format.formatter -> 'a list -> unit
 end

type query
type program
type index

val query_of_ast : program -> term -> query
val program_of_ast : ?print:bool -> decl list -> program
val execute_once : program -> query -> bool (* true means error *)
val execute_loop : program -> query -> unit

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
  | UVar of term attributed_ref * (*depth:*)int * (*argsno:*)int
  | AppUVar of term attributed_ref * (*depth:*)int * term list
  (* Misc: $custom predicates, ... *)
  | Custom of constant * term list
  | String of Func.t
  | Int of int
  | Float of float
and 'a attributed_ref = {
  mutable contents : 'a;
  mutable rest : constraint_ list
}
and constraint_ =
 (* exn is the constraint;
    the associated list is the list of variables the constraint is
    associated to *)
  cstr * term attributed_ref list (* well... open type in caml < 4.02 *)
and cstr =
 | Delayed_goal of dg
 | Delayed_unif of int * term array * int * term * term
and dg
and mode = bool list

val term_of_ast : depth:int -> Elpi_ast.term -> term
val oref : 'a -> 'a attributed_ref
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
  val string_of_constant : constant -> string

  val eqc : constant
  val orc : constant
  val andc : constant
  val andc2 : constant
  val rimplc : constant

  (* Value for unassigned UVar/Arg *)
  val dummy : term
 end

(* Custom predicates like $print. Must either raise No_clause or succeed
   with the list of new goals *)
val register_custom :
  string ->
  (depth:int -> env:term array -> index -> term list -> term list) ->
  unit

(* Functions useful to implement custom predicates and evaluable functions *)
val deref_uv : ?avoid:term attributed_ref -> from:constant -> to_:constant -> int -> term -> term
val deref_appuv : ?avoid:term attributed_ref -> from:constant -> to_:constant -> term list -> term -> term
val is_flex : term -> term attributed_ref option
val print_delayed : unit -> unit
val delay_goal : depth:int -> index -> goal:term -> on:term attributed_ref list -> unit
val declare_constraint : depth:int -> index -> goal:term -> on:term attributed_ref list -> unit

val lp_list_to_list : term -> term list

module ConstMap : Map.S with type key = Elpi_ast.Func.t
val query_of_ast_cmap :
  constant ->
  term ConstMap.t ->
  Elpi_ast.term -> string list * int * term array * term
val split_conj : term -> term list
