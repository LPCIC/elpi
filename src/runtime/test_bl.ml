open Elpi_runtime.Bl
let size = min Sys.max_array_length 9999999

let test_build () =
  Gc.minor (); Gc.major ();

  let t0 = Unix.gettimeofday () in
  let rec aux n acc =
    (* Format.eprintf "bl before adding %d = %a\n" n pp acc; *)
    if n = 0 then acc else aux (n-1) (rcons n acc) in
  let r1 = aux size (empty ()) in
  let t1 = Unix.gettimeofday () in

  Gc.minor (); Gc.major ();

  let t2 = Unix.gettimeofday () in
  let rec aux n acc =
    if n = 0 then acc else aux (n-1) (n :: acc) in
  let r2 = List.rev @@ aux size [] in
  let t3 = Unix.gettimeofday () in

  Format.eprintf "build: bl=%4f l=%4f\n" (t1-.t0) (t3-.t2);
  (* Format.eprintf "bl=%a\n" pp r1; *)
  r1, r2
;;

let _ = test_build ()