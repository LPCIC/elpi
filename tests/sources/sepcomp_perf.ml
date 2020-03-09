let us = {|

main :- p0, p1, p2, p3, p4, p5, p6, p7, p8, p9.

|}

let ex = {|

p0 :- print "ok".
p1 :- print "ok".
p2 :- print "ok".
p3 :- print "ok".
p4 :- print "ok".
p5 :- print "ok".
p6 :- print "ok".
p7 :- print "ok".
p8 :- print "ok".
p9 :- print "ok".

|}

open Elpi.API

(* XXX 4.06: List.init *)
let rec list_init i n f =
  if i >= n then [] else
  f i :: list_init (i+1) n f

let () =
  let open Sepcomp.Sepcomp_template in
  let elpi = init () in
  let flags = Compile.default_flags in
  let us = cc ~elpi ~flags 1 us in
  let ex = cc ~elpi ~flags 2 ex in
  let p = Compile.assemble ~elpi (us :: list_init 0 50000 (fun _ -> ex)) in
  let q = Compile.query p (Parse.goal_from ~elpi ~loc:(Ast.Loc.initial "g") (Lexing.from_string "main")) in
  exec q
