let u = {|

main :- not(p 1), p 2.

|};
;;

let () =
  let open Sepcomp.Sepcomp_template in
  let open Elpi.API in
  let elpi = init () in
  let flags = Compile.default_flags in
  let u0 = Marshal.from_channel (open_in_bin "_log/sepcomp7.unit") in
  let u1 = Marshal.from_channel (open_in_bin "_log/sepcomp8.unit") in
  let p = List.fold_left (fun base u -> Compile.extend ~base u) (Compile.empty_base ~elpi) [u0;u1] in
  let _,u2 = cc ~elpi ~flags ~base:p 0 u in
  let p = List.fold_left (fun base u -> Compile.extend ~base u) p [u2] in
  exec (query ~elpi p)
