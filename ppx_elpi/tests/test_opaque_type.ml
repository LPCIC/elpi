let elpi_stuff = ref []

let pp_simple _ _ = ()
type simple
[@@deriving elpi { append = elpi_stuff }]

open Elpi.API

[@@@warning "-26-27-32-39-60"]
let rec test : type h c . depth:int -> h -> c -> State.t -> RawData.term -> State.t * simple * Conversion.extra_goals =
  elpi_readback_simple

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !elpi_stuff

let main () =
  let _elpi, _ = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()