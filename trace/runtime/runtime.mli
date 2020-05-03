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

val set_cur_pred : string option -> unit
val get_cur_step : string -> int

val log : string -> string -> int -> unit

val debug : bool ref
val parse_argv : string list -> string list
val usage: string

(* prints here *)
type trace_format = TTY | JSON
val set_trace_output : trace_format -> Format.formatter -> unit
