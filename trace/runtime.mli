(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - 2017 Enrico Tassi <enrico.tassi@inria.fr>               *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* This is the runtime needed by trace_ppx *)

exception TREC_CALL of Obj.t * Obj.t (* ('a -> 'b) * 'a *)

val enter : string ->  (Format.formatter -> unit) -> unit
val print : string -> (Format.formatter -> 'a -> unit) -> 'a -> unit
val exit : string -> bool -> ?e:exn -> float -> unit

val cur_pred : string option -> unit

val log : string -> string -> int -> unit

exception Unknown
val pr_exn : (exn -> string) -> unit

val debug : bool ref
val dverbose : bool ref

val get_cur_step : string -> int

val parse_argv : string list -> string list
val usage: string

(* prints here *)
val set_formatter : Format.formatter -> unit
