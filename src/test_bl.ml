open Elpi.Internal.Bl
let size = 9999999

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

let test_scan bl l =

  let t0 = Unix.gettimeofday () in
  assert(List.length bl = size);
  let t1 = Unix.gettimeofday () in

  let t2 = Unix.gettimeofday () in
  assert(List.length l = size);

  let t3 = Unix.gettimeofday () in

  Format.eprintf "scan: bl=%4f l=%4f\n" (t1-.t0) (t3-.t2)

;;

let bl,l = test_build ()
let () = test_scan (bl |> to_scan |> to_list) l

(* let _ =
  let l = empty () in
  let l = rcons 10 l in
  let l = rcons 11 l in
  let l = insert (fun x -> 10 -x) 9 l in
  let l = rcons 12 l in
  let l = to_list @@ to_scan l in
  assert(l = [10;9;11;12])
;;

let _ =
  let l = empty () in
  let l = rcons 10 l in
  let l = rcons 11 l in
  let l = insert (fun x -> x - 11) 9 l in
  let l = rcons 12 l in
  let l = to_list @@ to_scan l in
  assert(l = [10;11;9;12])
;;


let _ =
  let l = empty () in
  let l = rcons 8 l in
  let l = rcons 10 l in
  let l as old = rcons 11 l in

  assert(to_list @@ to_scan old = [8;10;11]);
  let l = insert (fun x -> x - 10) 9 l in

  let l = to_list @@ to_scan l in
  assert(l = [8;10;9;11]);

  let l = to_list @@ to_scan old in
  assert(l = [8;10;11]);

;; *)
