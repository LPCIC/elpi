open Elpi_legacy_parser

module Make(C:Elpi_parser.Parse.Config) = struct

  let s = ref (Parser.init ~file_resolver:C.resolver)

  let program ~file = Parser.parse_program !s ~print_accumulated_files:false [file]
  let goal ~loc ~text = Parser.parse_goal ~loc text
  
  let program_from ~loc buf = Parser.parse_program_from_stream !s loc ~print_accumulated_files:false (Stream.from (fun i -> try Some (Lexing.lexeme_char buf i) with Invalid_argument _ -> None))
  let goal_from ~loc buf = Parser.parse_goal_from_stream ~loc (Stream.from (fun i -> try Some (Lexing.lexeme_char buf i) with Invalid_argument _ -> None))
end

let valid = true