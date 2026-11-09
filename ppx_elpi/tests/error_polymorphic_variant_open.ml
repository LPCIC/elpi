let declaration = Elpi.API.PPX.empty_declaration ()
type t = [> `A | `B of int ]
[@@deriving elpi { declaration }]
