val enter : string ->  (Format.formatter -> unit) -> unit
val print : string -> (Format.formatter -> 'a -> unit) -> 'a -> unit
val exit : ?e:exn -> float -> unit

exception Unknown
val pr_exn : (exn -> string) -> unit

val debug : bool ref
val first_step : int ref
val last_step : int ref
val init : ?first:int -> ?last:int -> bool -> unit
