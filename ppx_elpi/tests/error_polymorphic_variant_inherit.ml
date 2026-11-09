let declaration = Elpi.API.PPX.empty_declaration ()
type s = [ `A ]
type t = [ s | `B of int ]
[@@deriving elpi { declaration }]
