let u = {|

:name "this" p 1.

|}
;;

let () =
  let open Sepcomp.Sepcomp_template in
  let elpi = init () in
  let flags = Elpi.API.Compile.default_flags in
  let u = cc ~elpi ~flags 0 u in
  Marshal.to_channel (open_out_bin "_log/sepcomp7.unit") u [];
  exit 0
