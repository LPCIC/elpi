let declaration = Elpi.API.PPX.empty_declaration ()
module S = struct include String let pp _ _ = () let show _ = "" end

type tctx = Entry of (string[@elpi.key "term"]) * (string[@elpi.key "term"])
[@@elpi.index (module S)]
[@@deriving elpi { declaration }]
