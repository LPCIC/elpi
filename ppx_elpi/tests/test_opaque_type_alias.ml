let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

type simple = bool [@@elpi.opaque {
  OpaqueData.name = "simple"; doc = "";
  pp = (fun fmt _ -> Format.fprintf fmt "<simple>");
  compare = Stdlib.compare; hash = Hashtbl.hash;
  hconsed = false; constants = []; } ]
[@@deriving show, elpi { declaration }]

let simple :
    'h.
    (simple, #PPX.ctx as 'h, 'c)
      ContextualConversion.t = simple

let builtin = BuiltIn.declare ~file_name (PPX.to_list declaration)

let () = Ppx_tests_lib.check_declarations builtin
