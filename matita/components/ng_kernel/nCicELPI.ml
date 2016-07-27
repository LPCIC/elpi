module LP = Elpi_runtime

let _ =
   Printf.printf "LP.register_custom\n%!";
   LP.register_custom "$pippo" (fun ~depth:_ ~env:_ _ ts -> ts)
