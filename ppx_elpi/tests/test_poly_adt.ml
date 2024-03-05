let elpi_stuff = ref []

let pp_simple _ _ _ = ()
type 'a simple = A | B of int | C of 'a list * int
[@@deriving elpi { declaration = elpi_stuff } ]

let t1 : 'a 'c 'csts. ('a, #Elpi.API.ContextualConversion.ctx as 'c, 'csts) Elpi.API.ContextualConversion.t -> ('a simple, #Elpi.API.ContextualConversion.ctx as 'c, 'csts) Elpi.API.ContextualConversion.t = simple

class type o = object inherit Elpi.API.ContextualConversion.ctx method foobar : bool end

let t2 :  (int simple, o, Elpi.API.Data.constraints) Elpi.API.ContextualConversion.t = simple Elpi.API.BuiltInContextualData.int
let t3 :  (float simple, o, Elpi.API.Data.constraints) Elpi.API.ContextualConversion.t = simple Elpi.API.BuiltInContextualData.float

open Elpi.API

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !elpi_stuff

let main () =
  let _elpi = Setup.init ~builtins:[builtin] () in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()
