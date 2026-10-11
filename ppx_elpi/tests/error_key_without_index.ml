let declaration = Elpi.API.PPX.empty_declaration ()

type tctx = Entry of (string[@elpi.key "term"]) * bool
[@@deriving elpi { declaration }]
