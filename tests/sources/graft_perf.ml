(* Many grafts (:before, :after, :replace) in a long list of rules for the same
   key, near its end, and in a predicate indexed on many keys, where :replace
   looks for the rule in the list of every key. The cost of an edit must not
   depend on what comes before the edited rule, nor on the lists that do not
   contain it. *)

let rules = 20000
let keys = 5000
let grafts = 1000

let buf = Buffer.create 1_000_000
let line fmt = Printf.kbprintf (fun b -> Buffer.add_char b '\n') buf fmt

let () =
  line "pred p int -> int.";
  line "pred q -> int, int.";
  (* p: a long list of rules for the key 0 *)
  for i = 0 to rules - 1 do line {|:name "p%d" p 0 %d.|} i i done;
  for j = 0 to grafts - 1 do
    let k = rules - 1 - (j * 7919 mod (rules / 20)) in
    line {|:%s "p%d" p 0 %d.|} (if j mod 2 = 0 then "before" else "after") k (-j - 1)
  done;
  for i = 0 to (grafts / 2) - 1 do
    let k = rules - (rules / 10) + i in
    line {|:replace "p%d" p 0 %d.|} k k
  done;
  (* q: one rule per key, then more rules for some of the keys *)
  for i = 0 to keys - 1 do line {|:name "q%d" q %d %d.|} i i i done;
  for j = 0 to grafts - 1 do
    let k = j * 7919 mod keys in
    line {|:%s "q%d" q %d %d.|} (if j mod 2 = 0 then "before" else "after") k k (-j - 1)
  done;
  for i = 0 to (grafts / 2) - 1 do
    let k = (2 * i) + 1 in
    line {|:replace "q%d" q %d %d.|} k k k
  done;
  line "main :-";
  line "  std.findall (p 0 _) P, std.length P %d," (rules + grafts);
  line "  std.findall (q _ _) Q, std.length Q %d." (keys + grafts)

open Elpi.API

let () =
  let open Sepcomp.Sepcomp_template in
  let elpi = init () in
  let flags = Compile.default_flags in
  let p, _ = cc ~elpi ~flags ~base:(Compile.empty_base ~elpi) 1 (Buffer.contents buf) in
  let q = ok_query @@ Compile.query p (ok_goal ~elpi "main") in
  exec q
