let declaration = Elpi.API.PPX.empty_declaration ()
module S = struct include String let pp _ _ = () let show _ = "" end

type 'a tctx = Entry of (string[@elpi.key "term"]) * 'a
[@@elpi.index (module S)]
[@@deriving elpi { declaration }]
