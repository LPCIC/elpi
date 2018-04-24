(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
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
val execute_once : ?max_steps:int -> executable -> outcome
val execute_loop : executable -> more:(unit -> bool) -> pp:(float -> outcome -> unit) -> unit

(* Functions useful to implement built-in predicates and evaluable functions *)
val deref_uv : ?avoid:uvar_body -> from:constant -> to_:constant -> int -> term -> term
val deref_appuv : ?avoid:uvar_body -> from:constant -> to_:constant -> term list -> term -> term
val deref_head : depth:int -> term -> term
val is_flex : depth:int -> term -> uvar_body option
val pp_stuck_goal : Fmt.formatter -> stuck_goal -> unit

val lp_list_to_list : depth:int -> term -> term list
val list_to_lp_list : term list -> term

val split_conj : depth:int -> term -> term list

val mkAppArg : int -> int -> term list -> term
val move : 
  adepth:int -> env ->
  ?avoid:uvar_body -> ?depth:int ->
  from:int -> to_:int -> term -> term
val hmove : 
  ?avoid:uvar_body ->
  from:int -> to_:int -> term -> term
val subst: depth:int -> term list -> term -> term

val make_index : clause list -> idx
val clausify1 : mode Constants.Map.t -> nargs:int -> depth:int -> term -> clause * clause_src * int
val pp_key : key -> string

