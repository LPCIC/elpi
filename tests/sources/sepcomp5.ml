let u = {|

type x int.
type y int.
main :- p x.

|}
;;

let () =
  let open Sepcomp.Sepcomp_template in
  let _header = init () in
  let flags = Elpi.API.Compile.default_flags in
  let u = cc ~flags 0 u in
  Marshal.to_channel (open_out_bin "_log/sepcomp5.unit") u [];
  exit 0
