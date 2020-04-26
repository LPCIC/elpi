let elpi_stuff = ref []

let pp_simple _ _ _ = ()
type 'a simple = A | B of int | C of 'a * int
[@@deriving elpi { declaration = elpi_stuff } ]

class type o = object inherit Elpi.API.Conversion.ctx method foobar : bool end

let _ :  (int simple, o) Elpi.API.Conversion.t = simple Elpi.API.BuiltInData.int
let _ :  (float simple, o) Elpi.API.Conversion.t = simple Elpi.API.BuiltInData.float

open Elpi.API

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !elpi_stuff

let main () =
  let _elpi, _ = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()