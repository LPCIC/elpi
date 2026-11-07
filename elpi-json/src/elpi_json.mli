(* elpi-json: Yojson bindings for Elpi, the plugin json of findlib package
   elpi-json *)

(** [Yojson.Basic.t] as an ordinary variant, the Elpi type [json] *)
type t =
  | Null
  | Bool of bool
  | Int of int
  | Float of float
  | String of string
  | Assoc of (string * t) list
  | List of t list

(** the keys of an [`Assoc] are sorted *)
val of_yojson : Yojson.Basic.t -> t
val to_yojson : t -> Yojson.Basic.t

(** the Elpi type [json] *)
val json : t Elpi.API.Conversion.t

(** the builtins of the plugin, registered as ["json"] *)
val builtins : Elpi.API.Setup.builtins
