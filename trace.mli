(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

val enter : string ->  (Format.formatter -> unit) -> unit
val print : string -> (Format.formatter -> 'a -> unit) -> 'a -> unit
val exit : string -> ?e:exn -> float -> unit

exception Unknown
val pr_exn : (exn -> string) -> unit

val debug : bool ref
val init :
  ?where:(string * int * int) -> ?filter_out:string list -> bool -> unit
