(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Elpi_data

module Pp : sig
  val ppterm :
    ?min_prec:int -> int -> string list -> int -> env ->
       Format.formatter -> term -> unit
  val uppterm :
    ?min_prec:int -> int -> string list -> int -> env ->
       Format.formatter -> term -> unit
end

(* Interpreter API *)
val execute_once : ?max_steps:int -> program -> query -> outcome
val execute_loop : program -> query -> more:(unit -> bool) -> pp:(float -> outcome -> unit) -> unit

(* Functions useful to implement custom predicates and evaluable functions *)
val deref_uv : ?avoid:term_attributed_ref -> from:constant -> to_:constant -> int -> term -> term
val deref_appuv : ?avoid:term_attributed_ref -> from:constant -> to_:constant -> term list -> term -> term
val is_flex : depth:int -> term -> term_attributed_ref option
val print_constraints : unit -> unit
val print_delayed : unit -> unit
val pp_stuck_goal_kind : Fmt.formatter -> stuck_goal_kind -> unit

val lp_list_to_list : depth:int -> term -> term list
val list_to_lp_list : term list -> term

val split_conj : term -> term list

val llam_unify : int -> term array -> int -> term -> term -> bool

val mkAppArg : int -> int -> term list -> term
val move : 
  adepth:int -> env ->
  ?avoid:term_attributed_ref -> ?depth:int ->
  from:int -> to_:int -> term -> term

val make_index : clause list -> idx
val clausify : mode_decl Constants.Map.t -> int -> constant -> term -> clause list * int
val pp_key : key -> string

val get_custom_constraints : unit -> custom_constraints
val set_custom_constraints : custom_constraints -> unit

