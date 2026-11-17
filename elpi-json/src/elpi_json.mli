(* elpi-json: Yojson bindings for Elpi, the plugin json of findlib package
   elpi-json *)

(** [Yojson.Basic.t], the Elpi type [json]; the builtins that read a [json]
    sort the keys of an [`Assoc] ([Yojson.Basic.sort]) *)
type t = Yojson.Basic.t

(** the Elpi type [json] *)
val json : t Elpi.API.Conversion.t

(** the builtins of the plugin, registered as ["json"] *)
val builtins : Elpi.API.Setup.builtins
