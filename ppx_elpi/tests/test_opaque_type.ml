let elpi_stuff = ref []

let pp_simple _ _ = ()
type simple [@@elpi.opaque { Elpi.API.OpaqueData.
  name = "simple";
  cname = "simple";
  doc = "a simple opaque data type";
  pp = (fun fmt _ -> Format.fprintf fmt "<simple>");
  compare = Pervasives.compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}]
[@@deriving elpi { declaration = elpi_stuff }]

open Elpi.API

let test : 'h. (simple, #Conversion.ctx as 'h) Conversion.t = simple

let builtin = let open BuiltIn in
  declare ~file_name:(Sys.argv.(1)) !elpi_stuff

let main () =
  let _elpi, _ = Setup.init ~builtins:[builtin] ~basedir:"." [] in
  BuiltIn.document_file builtin;
  exit 0
;;

main ()
