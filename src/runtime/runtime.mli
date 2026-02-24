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
val deref_uv : ?oc:occur_check -> to_:int -> uvar -> int -> term
val deref_appuv : ?oc:occur_check -> to_:int -> uvar -> term list -> term
val deref_apparg : ?oc:occur_check -> from:int -> to_:int -> term -> term list -> term
val deref_head : depth:int -> term -> term
val eta_contract_flex : depth:int -> term -> term option
val is_flex : depth:int -> term -> uvar option

val expand_uv : depth:int -> uvar -> ano:int -> term
val expand_appuv : depth:int -> uvar -> args:term list -> term

val lp_list_to_list : depth:int -> term -> term list
val list_to_lp_list : term list -> term

val split_conj : depth:int -> term -> term list

val mkinterval : int -> int -> int -> term list
val mkConst : constant -> term
val mkAppL : constant -> term list -> term

val mkAppArg : int -> int -> term list -> term
val move : 
  argsdepth:int -> env ->
  ?oc:occur_check ->
  from:int -> to_:int -> term -> term
val hmove : 
  ?oc:occur_check ->
  from:int -> to_:int -> term -> term
val subst: depth:int -> term list -> term -> term

(* The projection from the internal notion of constraints in the API one *)
val get_suspended_goal : blockers -> 'a stuck_goal_kind -> suspended_goal option

val full_deref : depth:int -> term -> term

(* for testing *)
val lex_insertion : int list -> int list -> int

(* Some parts of the runtime are needed at compile time, like indexing *)
module CompileTime : sig
  (* updates how predicates are indexed *)
  val update_indexing :
    pred_info Constants.Map.t ->
      index -> index

  (* adds 1 clause to its index *)
  val add_to_index :
    det_check: float ref option -> (* update det checking info *)
    depth:int ->
    predicate:constant ->
    graft:Elpi_parser.Ast.Structured.insertion option ->
    clause -> string option -> index -> pred_info -> index * (overlap_clause option * pred_info)

  (* can raise CannotDeclareClauseForBuiltin *)
  val clausify1 :
    tail_cut:bool ->
    loc:Loc.t ->
    modes:(constant -> Mode.hos) -> (* for caching it in the clause *)
    nargs:int -> depth:int -> term -> (constant * clause) * clause_src * int


  val get_clauses : depth:int -> term -> overlap_clause Discrimination_tree.t -> overlap_clause Bl.scan

  val fresh_uvar : depth:int -> uvar
end

module Indexing : sig
  val add1clause_overlap_runtime : depth:constant -> pred_info Constants.Map.t -> constant -> time:constant -> clause -> overlap_clause option * pred_info Constants.Map.t
end
