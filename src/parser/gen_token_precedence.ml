open Elpi_lexer_config.Lexer_config

let pp_mehir_fixity fmt = function
  | Infix | Postfix | Prefix -> Format.fprintf fmt "nonassoc"
  | Infixl -> Format.fprintf fmt "left"
  | Infixr -> Format.fprintf fmt "right"

let pp_token_names fmt l =
  l |> List.iter (function
    | Fixed { token; _ } -> Format.fprintf fmt "%s " token
    | Extensible { token; _ } -> Format.fprintf fmt "%s " token)

let () =
  Format.printf "%%right BIND\n";
  mixfix_symbols |> List.iter (fun { fixity; tokens; _ } ->
    Format.printf "%%%a %a\n" pp_mehir_fixity fixity pp_token_names tokens);
  Format.printf "%%%%\n"
