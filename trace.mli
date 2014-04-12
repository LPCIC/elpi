(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

val enter : string ->  (Format.formatter -> unit) -> unit
val print : string -> (Format.formatter -> 'a -> unit) -> 'a -> unit
val exit : ?e:exn -> float -> unit

exception Unknown
val pr_exn : (exn -> string) -> unit

val debug : bool ref
val first_step : int ref
val last_step : int ref
val init : ?first:int -> ?last:int -> bool -> unit
