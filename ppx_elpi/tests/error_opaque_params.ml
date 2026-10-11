let declaration = Elpi.API.PPX.empty_declaration ()

type 'a o [@@elpi.opaque { Elpi.API.OpaqueData.name = "o"; doc = "";
  pp = (fun fmt _ -> ()); compare = Stdlib.compare; hash = Hashtbl.hash;
  hconsed = false; constants = []; } ]
[@@deriving elpi { declaration }]
