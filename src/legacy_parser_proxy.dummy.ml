module Make(C:Elpi_parser.Parse.Config) = struct
  let program ~file:_ = assert false
  let goal ~loc:_ ~text:_ = assert false
  let program_from ~loc:_ _ = assert false
  let goal_from ~loc:_ _ = assert false
end
let valid = false