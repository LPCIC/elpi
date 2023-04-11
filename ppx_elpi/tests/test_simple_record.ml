let elpi_stuff = ref []

let pp_simple _ _ = ()
type simple = { f : int; g : bool }
[@@deriving elpi { declaration = elpi_stuff }]

open Elpi.API

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !elpi_stuff

let main () =
  let _elpi, _ = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()