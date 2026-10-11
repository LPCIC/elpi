let declaration = Elpi.API.PPX.empty_declaration ()
module S = struct include String let pp _ _ = () let show _ = "" end

type a = A of (string[@elpi.key "a"]) [@@elpi.index (module S)]
and b = B of (string[@elpi.key "b"]) [@@elpi.index (module S)]
[@@deriving elpi { declaration }]
