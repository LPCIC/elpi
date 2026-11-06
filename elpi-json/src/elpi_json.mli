(* elpi-json: Yojson bindings for Elpi, the plugin of package elpi-json *)

(** the Elpi type [json] of [Yojson.Basic.t] *)
val json : Yojson.Basic.t Elpi.API.Conversion.t

(** the builtins of the plugin, registered as ["elpi-json"] *)
val builtins : Elpi.API.Setup.builtins
