let u = {|

pred p i:int.
:remove "this" p _.

p 2.

|}
;;

let () =
  let open Sepcomp.Sepcomp_template in
  let open Elpi.API in
  let elpi = init () in
  let flags = Compile.default_flags in
  let u0 = Marshal.from_channel (open_in_bin "_log/sepcomp7.unit") in
  let base = Compile.extend ~flags ~base:(Compile.empty_base ~elpi) u0 in
  let _,u = cc ~elpi ~flags ~base 0 u in
  Marshal.to_channel (open_out_bin "_log/sepcomp8.unit") u [];
  exit 0
