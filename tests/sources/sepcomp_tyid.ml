let p1 = {|
  pred p o:int.
  p 1.
|}

let p2 = {|
  pred p o:int.
  p 2.
|}

let maine = "pred p o:int. main :- std.findall (p _) L, print L."

open Elpi.API

let () =
  let open Sepcomp.Sepcomp_template in
  let elpi = init () in
  let flags = Compile.default_flags in
  let pmain,_ = cc ~elpi ~flags ~base:(Compile.empty_base ~elpi) 1 maine in
  let _,unit1 = cc ~elpi ~flags ~base:(Compile.empty_base ~elpi) 2 p1 in
  let _,unit2 = cc ~elpi ~flags ~base:(Compile.empty_base ~elpi) 3 p2 in

  let cp = Compile.extend ~base:pmain unit1 in
  let cp = Compile.extend ~base:cp unit2 in

  let q = Compile.query cp (Parse.goal_from ~elpi ~loc:(Ast.Loc.initial "g") (Lexing.from_string "main")) in
  exec q
