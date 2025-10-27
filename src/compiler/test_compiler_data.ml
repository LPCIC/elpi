let pp_ta t s =
  let open Elpi_compiler.Compiler_data in
  let s' = Format.asprintf "@[%a@]" TypeAssignment.pretty_mut_once t in
  if s <> s' then begin
    Format.eprintf "Unexpected print: %a\nactual: %a\nreference: %s\n"
      TypeAssignment.pp (Val t) TypeAssignment.pretty_mut_once t s;
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
let arro s t = Arr(TypeAssignment.MVal Ast.Mode.Output,NotVariadic,s,t)
let arri s t = Arr(TypeAssignment.MVal Ast.Mode.Input,NotVariadic,s,t)

let () = pp_ta (Prop Relation) "(pred)";;
let () = pp_ta (Prop Function) "(func)";;
let () = pp_ta (list int) "list int";;
let () = pp_ta (arro (list int) int) "list int -> int";;
let () = pp_ta (arri (list int) int) "list int -> int";;
let () = pp_ta (list (list int)) "list (list int)";;
let () = pp_ta (arri int (arro (list (list int)) (Prop Function))) "(func int -> list (list int))";;
let () = pp_ta (arro int (arro (list (list int)) (Prop Function))) "(func -> int, list (list int))";;
let () = pp_ta (arro int (arri (list (list int)) (Prop Function))) "(pred o:int, i:list (list int))";;
let () = pp_ta (arri int (arro (list (list int)) (Prop Relation))) "(pred i:int, o:list (list int))";;

(* let () = pp_ta (arr (list int) int) "o:list int -> int";;
let () = pp_ta (arr (arr int int) int) "o:(o:int -> int) -> int";;
let () = pp_ta (arr int (arr int int)) "o:int -> o:int -> int";;
let () = pp_ta (arr int (arr (list int) int)) "o:int -> o:list int -> int";;
let () = pp_ta (list (arr int int)) "list (o:int -> int)";; *)

open ScopedTerm

let loc = Ast.Loc.initial "x"
let ty  = TypeAssignment.create (Prop Relation)
let c3 = { loc; it = CData (Ast.cint.cin 3); ty };;
let lam v t = { loc; ty; it = Lam(Some(ScopedTerm.mk_binder ~lang:"" (F.from_string v) ~loc),None,t)}
let var v = { loc; ty; it = App(ScopedTerm.mk_bound_const ~lang:"" (F.from_string v) ~loc,[])}
let app c l = { loc; ty; it = App(ScopedTerm.mk_global_const ~escape_ns:true (F.from_string c) ~loc,l)}

let () = pp_t c3 "3";;
let () = pp_t (app "f" [app "g" [var "x"]]) "f (g x)";;
let () = pp_t (lam "x" (var "x")) "x\\ x";;
let () = pp_t (app "pi" [lam "x" (var "x")]) "pi x\\ x";;
let () = pp_t (app "q" [lam "x" (var "x"); app "f" [var "x"]]) "q (x\\ x) (f x)";;
let () = pp_t (app "q" [lam "x" (var "x")]) "q (x\\ x)";;
