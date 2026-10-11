let declaration = Elpi.API.PPX.empty_declaration ()
type tctx = Entry of (string[@elpi.key "term"]) [@@elpi.index (module String)]
[@@deriving elpi { declaration }]

type term = Var of string [@elpi.var tctx] [@elpi.readback fun ~depth _ _ _ -> assert false] [@elpi.embed fun ~depth _ _ _ -> assert false]
[@@deriving elpi { declaration }]
