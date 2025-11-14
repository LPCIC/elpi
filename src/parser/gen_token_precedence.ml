open Elpi_lexer_config.Lexer_config

let pp_mehir_fixity fmt = function
  | Infix | Postfix | Prefix -> Format.fprintf fmt "nonassoc"
  | Infixl -> Format.fprintf fmt "left"
  | Infixr -> Format.fprintf fmt "right"

let pp_token_names fmt l =
  let toks = l |> List.map (function
    | Fixed { token; _ } -> Format.asprintf "%s" token
    | Extensible { token; _ } -> Format.asprintf "%s" token) in
  let toks = Elpi_util.Util.uniq @@ List.sort Stdlib.compare toks in
  Format.fprintf fmt "%s" (String.concat " " toks)

let () =
  Format.printf "%%right BIND\n";
  mixfix_symbols |> List.iter (fun { fixity; tokens; _ } ->
    Format.printf "%%%a %a\n" pp_mehir_fixity fixity pp_token_names tokens);
  Format.printf "%%%%\n"
