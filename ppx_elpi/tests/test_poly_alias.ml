let elpi_stuff = ref []

let pp_simple _ _ _ = ()
type 'a simple = 'a * int
[@@deriving elpi { declaration = elpi_stuff }]

open Elpi.API

let x : 'a 'c 'csts. ('a, 'c,'csts) ContextualConversion.t -> ('a simple, 'c, 'csts) ContextualConversion.t = simple

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !elpi_stuff

let main () =
  let _elpi = Setup.init ~builtins:[builtin] () in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()
