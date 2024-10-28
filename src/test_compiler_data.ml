let pp_ta t s =
  let open Elpi.Internal.Compiler_data in
  let s' = Format.asprintf "%a" TypeAssignment.pretty t in
  if s <> s' then begin
    Format.eprintf "Unexpected print: %a\nactual: %a\nreference: %s\n"
      TypeAssignment.pp (Val t) TypeAssignment.pretty t s;
    exit 1
  end
;;

open Elpi
open Internal
open Compiler_data
open TypeAssignment
open Elpi_parser

let list x = (App(F.from_string "list",x,[]))
let int = Cons (F.from_string "int")
let arr s t = Arr(Ast.Structured.NotVariadic,s,t)

let () = pp_ta Prop "prop";;
let () = pp_ta (list int) "list int";;
let () = pp_ta (list (list int)) "list (list int)";;
let () = pp_ta (arr (list int) int) "list int -> int";;
let () = pp_ta (arr (arr int int) int) "(int -> int) -> int";;
let () = pp_ta (arr int (arr int int)) "int -> int -> int";;
let () = pp_ta (arr int (arr (list int) int)) "int -> list int -> int";;
let () = pp_ta (list (arr int int)) "list (int -> int)";;