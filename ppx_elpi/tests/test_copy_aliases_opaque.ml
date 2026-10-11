let file_name = Sys.argv.(1)

(* The deep copy of type abbreviations and of opaque types, used as the fields
   of another type *)

open Elpi.API

let declaration = PPX.empty_declaration ()

type id = string
[@@deriving show, elpi { declaration }]

type 'a counted = 'a * int
[@@deriving show, elpi { declaration }]

let pp_secret fmt _ = Format.fprintf fmt "<secret>"
type secret [@@elpi.opaque {
  OpaqueData.name = "secret"; doc = "";
  pp = pp_secret;
  compare = Stdlib.compare; hash = Hashtbl.hash;
  hconsed = false; constants = []; } ]
[@@deriving elpi { declaration }]

type entry = E of id * secret * float counted
[@@deriving show, elpi { declaration }]

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let () = Ppx_tests_lib.check_declarations builtin
