let elpi_stuff = ref []

let pp_simple _ _ = ()
let pp_mut _ _ = ()
type simple = A | B of int * mut
and mut = C | D of simple
[@@deriving elpi { declaration = elpi_stuff }]

open Elpi.API

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !elpi_stuff

let main () =
  let _elpi = Setup.init ~builtins:[builtin] () in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()