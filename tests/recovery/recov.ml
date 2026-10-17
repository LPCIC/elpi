(* recov DIR   runs the error-resilient parser on the *.elpi files of DIR and
               prints the syntax errors (line:column and message), then the
               kind of each declaration that survives
   recov --same FILE...
               checks that the files parse without errors *)
open Elpi_util
open Elpi_parser

let parser_for dir =
  (module Parse.Make (struct
    let versions = Util.StrMap.empty
    let resolver = Util.std_resolver ~paths:[ dir ] ()
  end) : Parse.Parser_w_Internals)

let read file =
  let ic = open_in_bin file in
  let text = really_input_string ic (in_channel_length ic) in
  close_in ic;
  text

let resilient (module P : Parse.Parser_w_Internals) file =
  let text = read file in
  P.program_from ~loc:(Util.Loc.initial file) ~digest:(Digest.string text) (Lexing.from_string text)

let kind (d : Ast.Program.decl) =
  match d with
  | Clause _ -> "clause" | Chr _ -> "rule" | Macro _ -> "macro" | Kind _ -> "kind"
  | Type _ -> "type" | Pred _ -> "pred" | TypeAbbreviation _ -> "typeabbrev"
  | Ignored _ -> "ignored" | Constraint _ -> "constraint" | Namespace _ -> "namespace"
  | Shorten _ -> "shorten" | Accumulated _ -> "accumulate" | Begin _ -> "{" | End _ -> "}"

let cases dir =
  let p = parser_for dir in
  Sys.readdir dir |> Array.to_list |> List.filter (fun f -> Filename.check_suffix f ".elpi")
  |> List.sort compare
  |> List.iter (fun f ->
      Printf.printf "== %s\n" f;
      let { Ast.ast; _ }, errors = resilient p (Filename.concat dir f) in
      List.iter (fun { Util.loc; message; _ } ->
          match loc with
          | Some { Util.Loc.line; source_start; line_starts_at; _ } ->
              Printf.printf "ERROR %d:%d %s\n" line (source_start - line_starts_at)
                (String.concat " " (List.filter (( <> ) "") (String.split_on_char '\n' (String.trim message))))
          | None -> Printf.printf "ERROR %s\n" message) errors;
      List.iter (fun d -> print_endline (kind d)) ast)

let same files =
  List.iter (fun file ->
    let p = parser_for (Filename.dirname file) in
    let _, errors = resilient p file in
    if errors = [] then Printf.printf "ok %s\n" file else Printf.printf "ERRORS %s\n" file)
    files

let () =
  match Array.to_list Sys.argv with
  | _ :: "--same" :: files -> same files
  | [ _; dir ] -> cases dir
  | _ -> prerr_endline "usage: recov DIR | recov --same FILE..."; exit 2
