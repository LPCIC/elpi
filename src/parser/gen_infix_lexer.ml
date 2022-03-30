
open Elpi_lexer_config.Lexer_config
open Re

let pp_fixed fmt l =
  l |> List.iter (fun x -> Format.fprintf fmt "| %S " x)

let pp_tokens fmt l =
  l |> List.iter (function
    | Fixed { token; the_token; _ } ->
        Format.fprintf fmt "  | %S { %s }@;" the_token token
    | Extensible { start; token; fixed; at_least_one_char; _ } ->
        let next = if at_least_one_char then "symbcharplus" else "symbcharstar" in
        Format.fprintf fmt "  | ( %S %s %a) as x { %s x }@;" start next pp_fixed fixed token)

let lexing_rules =
  let open Format in
  let b = Buffer.create 100 in
  let fmt = formatter_of_buffer b in
  fprintf fmt "@[<v>(* generated *)@;";
  mixfix_symbols |> List.iter (fun { tokens; _ } ->
    fprintf fmt "%a" pp_tokens tokens);
  fprintf fmt "@;(* /generated *)@;@]";
  pp_print_flush fmt ();
  Buffer.contents b

let () =
  let template = Sys.argv.(1) in
  let ic = open_in template in
  try while true do
    let l = input_line ic in
    let l = Str.global_replace (Str.regexp_string "@@MIXFIX@@") lexing_rules l in
    Printf.printf "%s\n" l;
  done;
  with End_of_file -> () 