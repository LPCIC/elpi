let declaration = Elpi.API.PPX.empty_declaration ()
module S = struct include String let pp _ _ = () let show _ = "" end
type tctx = Entry of (string[@elpi.key "term"]) * bool [@@elpi.index (module S)]
[@@deriving elpi { declaration }]
type term = Var of string [@elpi.var tctx]
[@@deriving elpi { declaration; context = [] }]
