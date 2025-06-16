(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - 2017 Enrico Tassi <enrico.tassi@inria.fr>               *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* This is the runtime needed by trace_ppx *)

exception TREC_CALL of Obj.t * Obj.t (* ('a -> 'b) * 'a *)

type j = J : (Format.formatter -> 'a -> unit) * 'a -> j

val enter : runtime_id:int -> string ->  (Format.formatter -> unit) -> unit
val info : runtime_id:int -> ?goal_id:int -> string -> j list -> unit
val exit : runtime_id:int -> string -> bool -> exn option -> float -> unit
val end_trace : runtime_id:int -> unit

val set_cur_pred : string option -> unit
val get_cur_step : runtime_id:int -> string -> int
val incr_cur_step : runtime_id:int -> string -> unit

val log : runtime_id:int -> string -> string -> int -> unit

val debug : bool ref
val parse_argv : string list -> string list
val usage: string

(* prints here *)
type trace_format = TTY | JSON
val set_trace_output : trace_format -> Format.formatter -> unit

module JSON : sig
  val pp_s : Format.formatter -> string -> unit
  val pp_b : Format.formatter -> bool -> unit
  val pp_i : Format.formatter -> int -> unit
  val pp_f : Format.formatter -> float -> unit
  val pp_kv : Format.formatter -> string * j -> unit
  val pp_j : Format.formatter -> j -> unit

  val pp_comma_l :
    Format.formatter ->
    (Format.formatter -> 'a -> unit) ->
    'a list ->
    unit

  val pp_a : Format.formatter -> j list -> unit
  val pp_d : Format.formatter -> (string * j) list -> unit

  module JSON_STRING_ENCODING : sig
    val write_string_body : Buffer.t -> string -> unit
  end
end