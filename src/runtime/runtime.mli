(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util

open Util
open Data

module Pp : sig

  val ppterm :
    ?pp_ctx:pp_ctx -> ?min_prec:int -> int -> string list -> argsdepth:int -> env ->
       Format.formatter -> term -> unit
  val uppterm :
    ?pp_ctx:pp_ctx -> ?min_prec:int -> int -> string list -> argsdepth:int -> env ->
       Format.formatter -> term -> unit

  val pp_constant : ?pp_ctx:pp_ctx -> Format.formatter -> constant -> unit
  val pp_oref : ?pp_ctx:pp_ctx -> Format.formatter -> (UUID.t * Obj.t) -> unit
end
val pp_stuck_goal : ?pp_ctx:pp_ctx -> Fmt.formatter -> stuck_goal -> unit

(* Interpreter API *)
val execute_once :
  ?max_steps:int -> ?delay_outside_fragment:bool -> executable -> 'a outcome
val execute_loop :
  ?delay_outside_fragment:bool -> executable -> more:(unit -> bool) -> pp:(float -> 'a outcome -> unit) -> unit

(* Functions useful to implement built-in predicates and evaluable functions *)
val deref_uv : ?avoid:uvar_body -> from:constant -> to_:constant -> int -> term -> term
val deref_appuv : ?avoid:uvar_body -> from:constant -> to_:constant -> term list -> term -> term
val deref_head : depth:int -> term -> term
val eta_contract_flex : depth:int -> term -> term option
val is_flex : depth:int -> term -> uvar_body option

val expand_uv : depth:int -> uvar_body -> lvl:int -> ano:int -> term
val expand_appuv : depth:int -> uvar_body -> lvl:int -> args:term list -> term

val lp_list_to_list : depth:int -> term -> term list
val list_to_lp_list : term list -> term

val split_conj : depth:int -> term -> term list

val mkinterval : int -> int -> int -> term list
val mkConst : constant -> term
val mkAppL : constant -> term list -> term

val mkAppArg : int -> int -> term list -> term
val move : 
  argsdepth:int -> env ->
  ?avoid:uvar_body ->
  from:int -> to_:int -> term -> term
val hmove : 
  ?avoid:uvar_body ->
  from:int -> to_:int -> term -> term
val subst: depth:int -> term list -> term -> term

(* The projection from the internal notion of constraints in the API one *)
val get_suspended_goal : 'a stuck_goal_kind -> suspended_goal option

val full_deref : depth:int -> term -> term

(* for testing *)
val lex_insertion : int list -> int list -> int

(* Some parts of the runtime are needed at compile time, like indexing *)
module CompileTime : sig
  (* updates how predicates are indexed *)
  val update_indexing :
    (Mode.hos * indexing) Constants.Map.t ->
      index -> index

  (* adds 1 clause to its index *)
  val add_to_index :
    depth:int ->
    predicate:constant ->
    graft:Elpi_parser.Ast.Structured.insertion option ->
    clause -> string option -> index -> index

  (* can raise CannotDeclareClauseForBuiltin *)
  val clausify1 :
    loc:Loc.t ->
    modes:(constant -> Mode.hos) -> (* for caching it in the clause *)
    nargs:int -> depth:int -> term -> (constant * clause) * clause_src * int

end
