let declaration = Elpi.API.PPX.empty_declaration ()
type t = A of (int * int * int * int * int)
[@@deriving elpi { declaration }]
