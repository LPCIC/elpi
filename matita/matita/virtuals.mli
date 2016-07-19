type symbol = Glib.unichar
type tag = string

val add_virtual: string list -> symbol -> tag list -> unit

exception Not_a_virtual
val symbol_of_virtual: string -> string * symbol

val get_all_virtuals : unit -> (tag * (string list * symbol) list) list

val add_eqclass: symbol list -> unit
val similar_symbols: symbol -> symbol list

val get_all_eqclass: unit -> symbol list list

(* (["\\lambda";"\\"], "λ", ["logics";"letters"]) *)
