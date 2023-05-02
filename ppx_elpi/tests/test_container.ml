let declaration = ref []

let pp_loc _ _ _ = ()

type 'a loc = {
  loc : int;
  data : 'a;
}
[@@deriving elpi { declaration }]

let pp_term _ _ = ()
type term =
  | A of int
  | B of string * bool
[@@deriving elpi { declaration }]

let pp_x _ _ = ()
type x = term loc * int
[@@deriving elpi { declaration }]

let xx : 'c 'csts. (x,'c,'csts) Elpi.API.ContextualConversion.t = x

open Elpi.API

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !declaration

let main () =
  let _elpi= Setup.init ~builtins:[builtin] () in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()