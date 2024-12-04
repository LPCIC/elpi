let pp_ta t s =
  let open Elpi_compiler.Compiler_data in
  let s' = Format.asprintf "@[%a@]" TypeAssignment.pretty t in
  if s <> s' then begin
    Format.eprintf "Unexpected print: %a\nactual: %a\nreference: %s\n"
      TypeAssignment.pp (Val t) TypeAssignment.pretty t s;
    exit 1
  end
;;

let pp_t t s =
  let open Elpi_compiler.Compiler_data in
  let s' = Format.asprintf "@[%a@]" ScopedTerm.pretty t in
  if s <> s' then begin
    Format.eprintf "Unexpected print: %a\nactual: %a\nreference: %s\n"
      ScopedTerm.pp t ScopedTerm.pretty t s;
    exit 1
  end
;;

open Elpi_compiler
open Compiler_data
open TypeAssignment
open Elpi_parser

let list x = (App(F.from_string "list",x,[]))
let int = Cons (F.from_string "int")
let arr s t = Arr(Ast.Structured.NotVariadic,s,t)

let () = pp_ta (Prop Relation) "prop";;
let () = pp_ta (Prop Function) "fprop";;
let () = pp_ta (list int) "list int";;
let () = pp_ta (list (list int)) "list (list int)";;
let () = pp_ta (arr (list int) int) "list int -> int";;
let () = pp_ta (arr (arr int int) int) "(int -> int) -> int";;
let () = pp_ta (arr int (arr int int)) "int -> int -> int";;
let () = pp_ta (arr int (arr (list int) int)) "int -> list int -> int";;
let () = pp_ta (list (arr int int)) "list (int -> int)";;

open ScopedTerm

let loc = Ast.Loc.initial "x"
let ty  = MutableOnce.create @@ Val (Prop Relation)
let c3 = { loc; it = CData (Ast.cint.cin 3); ty };;
let lam v t = { loc; ty; it = Lam(Some(F.from_string v,""),None,MutableOnce.make (F.from_string""),t)}
let var v = { loc; ty; it = Const(Bound "",F.from_string v)}
let app c l = { loc; ty; it = App(Scope.mkGlobal ~escape_ns:true (),F.from_string c,List.hd l,List.tl l)}

let () = pp_t c3 "3";;
let () = pp_t (app "f" [app "g" [var "x"]]) "f (g x)";;
let () = pp_t (lam "x" (var "x")) "x\\ x";;
let () = pp_t (app "pi" [lam "x" (var "x")]) "pi x\\ x";;
let () = pp_t (app "q" [lam "x" (var "x"); app "f" [var "x"]]) "q (x\\ x) (f x)";;
let () = pp_t (app "q" [lam "x" (var "x")]) "q (x\\ x)";;
