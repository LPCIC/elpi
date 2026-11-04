let size = 65536

let us = Printf.sprintf {|

pred p0 -> int.

main :- std.findall (p0 _) L, std.length L %d.

%s
|} (size + 1) (String.concat "\n" (List.init size (fun _ -> "p0 0.")))

let ex = {|

p0 1.

|}

open Elpi.API

(* Unlike the other sepcomp_perf tests, which extend the result of the previous
   extension, this one extends the same base many times, as a host does when it
   keeps a base program around: the clause lists must not be copied every time,
   in particular with an implementation of them based on arrays that double in
   size, of which this size is the worst case. *)
let () =
  let open Sepcomp.Sepcomp_template in
  let elpi = init () in
  let flags = Compile.default_flags in
  let base,_ = cc ~elpi ~flags ~base:(Compile.empty_base ~elpi) 1 us in
  let _,ex = cc ~elpi ~flags ~base 2 ex in
  let t0 = Unix.gettimeofday () in
  let rec extend i p =
    if i = 0 then p
    else extend (i-1) (ok (Compile.extend ~base ex)) in
  let p = extend 2000 base in
  Printf.printf "extend: %f\n%!" (Unix.gettimeofday () -. t0);
  let q = ok_query @@ Compile.query p (ok_goal ~elpi "main") in
  exec q
