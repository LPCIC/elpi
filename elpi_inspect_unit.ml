open Elpi.API

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <unit>\n\nPrints a marshaled unit.\n" (Filename.basename Sys.argv.(0));
    exit 1;
  end;
  let u : Compile.compilation_unit = Marshal.from_channel (open_in_bin Sys.argv.(1)) in
  Format.printf "%a" Compile.pp_compilation_unit u;
  exit 0