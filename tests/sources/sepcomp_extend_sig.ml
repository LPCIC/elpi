let u = {|

pred p i:int.
p 2 :- !, fail.

|}
;;

let v = {|

p _.

main :- p 2.

|}
;;

let () =
  let open Sepcomp.Sepcomp_template in
  let elpi = init () in
  let flags = Elpi.API.Compile.default_flags in
  let base = Elpi.API.Compile.empty_base ~elpi in
  let _, u = cc ~elpi ~flags ~base 0 u in
  let su = signature_of u in
  let p = extend_signature ~flags ~base su in
  let p, _ = cc ~elpi ~flags ~base:p 0 v in
  let q = query ~elpi p in
  exec q
