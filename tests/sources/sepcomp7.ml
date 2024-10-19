let u = {|

pred p i:int.

:name "this" p 1.

|}
;;

let () =
  let open Sepcomp.Sepcomp_template in
  let open Elpi.API in
  let elpi = init () in
  let flags = Compile.default_flags in
  let _, u = cc ~elpi ~flags ~base:(Compile.empty_base ~elpi) 0 u in
  Marshal.to_channel (open_out_bin "_log/sepcomp7.unit") u [];
  exit 0
