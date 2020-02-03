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
  let elpi = init () in
  let flags = Elpi.API.Compile.default_flags in
  let u0 = Marshal.from_channel (open_in_bin "_log/sepcomp5.unit") in
  let u1 = cc ~elpi ~flags 0 u in
  let p = link ~elpi [u0;u1] in
  exec  p
