
open Elpi_parser

module Make(C:Parse.Config) : Parse.Parser

(** compile time deps were available *)
val valid : bool