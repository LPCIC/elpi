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

val execute_once : print_constraints:bool -> program -> query -> bool (* true means error *)
val execute_loop : program -> query -> unit

(* Custom predicates like $print. Must either raise No_clause or succeed
   with the list of new goals *)
val register_custom :
  string ->
  (depth:int -> env:term array -> idx -> term list -> term list) ->
  unit

(* Functions useful to implement custom predicates and evaluable functions *)
val deref_uv : ?avoid:term_attributed_ref -> from:constant -> to_:constant -> int -> term -> term
val deref_appuv : ?avoid:term_attributed_ref -> from:constant -> to_:constant -> term list -> term -> term
val is_flex : depth:int -> term -> term_attributed_ref option
val print_delayed : unit -> unit
val delay_goal : depth:int -> idx -> goal:term -> on:term_attributed_ref list -> unit
val declare_constraint : depth:int -> idx -> goal:term -> on:term_attributed_ref list -> unit

val lp_list_to_list : depth:int -> term -> term list
val list_to_lp_list : term list -> term

val split_conj : term -> term list

val llam_unify : int -> term array -> int -> term -> term -> bool

val is_custom_declared : constant -> bool
val mkAppArg : int -> int -> term list -> term
val move : 
  adepth:int -> env ->
  ?avoid:term_attributed_ref -> ?depth:int ->
  from:int -> to_:int -> term -> term

val make_index : clause list -> idx
val clausify : mode_decl C.Map.t -> int -> constant -> term -> clause list * int
val pp_key : key -> string

