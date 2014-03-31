val enter : string -> string lazy_t -> unit
val exit : ?e:exn -> unit -> unit

exception Unknown
val pr_exn : (exn -> string) -> unit

val debug : bool ref
val first_step : int ref
val last_step : int ref
val init : ?first:int -> ?last:int -> bool -> unit
