let u = {|

type y int.
type x int.

pred p i:int.

p x :- print "ok".
p _ :- print "ko".

|};
;;

let () =
  let open Sepcomp.Sepcomp_template in
  let open Elpi.API in
  let elpi = init () in
  let flags = Compile.default_flags in
  let u0 = Marshal.from_channel (open_in_bin "_log/sepcomp5.unit") in
  let _, u1 = cc ~elpi ~flags  ~base:(Compile.empty_base ~elpi) 0 u in
  let p = List.fold_left (fun base u -> Compile.extend ~base u) (Compile.empty_base ~elpi) [u0;u1] in
  exec  (query ~elpi p)
