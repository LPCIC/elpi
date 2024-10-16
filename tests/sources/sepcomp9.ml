let u = {|

main :- not(p 1), p 2.

|};
;;

let () =
  let open Sepcomp.Sepcomp_template in
  let elpi = init () in
  let flags = Elpi.API.Compile.default_flags in
  let u0 = Marshal.from_channel (open_in_bin "_log/sepcomp7.unit") in
  let u1 = Marshal.from_channel (open_in_bin "_log/sepcomp8.unit") in
  let u2 = cc ~elpi ~flags 0 u in
  let p = link ~elpi [u0;u1;u2] in
  exec  p
