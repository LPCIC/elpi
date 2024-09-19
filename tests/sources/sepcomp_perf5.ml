let us = {|

main :- p0.

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
  let t0 = Unix.gettimeofday () in
  let elpi = init () in
  let flags = Compile.default_flags in
  let us = cc ~elpi ~flags 1 us in
  let ex = cc ~elpi ~flags 2 ex in
  let p = Compile.assemble ~elpi [us] in
  let t1 = Unix.gettimeofday () in
  Printf.printf "base: %f\n%!" (t1 -. t0);
  let exs = list_init 0 50000 (fun _ -> ex) in
  let rec extend i p =
    if i = 0 then p
    else extend (i-1) (Compile.extend ~base:p exs) in
  let p = extend 2 p in
  let t2 = Unix.gettimeofday () in
  Printf.printf "extend: %f\n%!" (t2 -. t1);
  let q = Compile.query p (Parse.goal_from ~elpi ~loc:(Ast.Loc.initial "g") (Lexing.from_string "main")) in
  let t3 = Unix.gettimeofday () in
  Printf.printf "query: %f\n%!" (t3 -. t2);
  let exe = Compile.optimize q in
  let t4 = Unix.gettimeofday () in
  Printf.printf "optimize: %f\n%!" (t4 -. t3);
  match Execute.once exe with
  | Execute.Failure -> exit 1
  | Execute.Success _ ->
       let t5 = Unix.gettimeofday () in
       Printf.printf "exec: %f\n%!" (t5 -. t4);
       exit 0
  | Execute.NoMoreSteps -> assert false


  