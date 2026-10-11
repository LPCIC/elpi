let declaration = Elpi.API.PPX.empty_declaration ()
type tctx = Entry of (string[@elpi.key "term"]) [@@elpi.index (module String)]
[@@deriving elpi { declaration }]

type term = Var of string * int [@elpi.var tctx]
[@@deriving elpi { declaration }]
