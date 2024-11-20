let elpi_stuff = ref []

let pp_simple _ _ = ()
type simple = A | B of int
[@@deriving elpi { declaration = elpi_stuff }]

open Elpi.API

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !elpi_stuff

let main () =
  let _elpi= Setup.init ~builtins:[builtin] () in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()