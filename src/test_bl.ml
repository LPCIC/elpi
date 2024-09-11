open Elpi.Internal.Bl
let size = 9999999

let test_build () =
  Gc.minor (); Gc.major ();
  
  let t0 = Unix.gettimeofday () in
  let rec aux n acc =
    (* Format.eprintf "bl before adding %d = %a\n" n pp acc; *)
    if n = 0 then acc else aux (n-1) (rcons n acc) in
  let r1 = commit @@ aux size (empty ()) in
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

  let rec len acc = function
    | Cons { head; tail } -> assert(head >= 0); len (acc+1) tail
    | Nil -> acc
  in
  let t0 = Unix.gettimeofday () in
  assert(len 0 bl = size);
  let t1 = Unix.gettimeofday () in

  let t2 = Unix.gettimeofday () in
  assert(List.length l = size);
  
  let t3 = Unix.gettimeofday () in

  Format.eprintf "scan: bl=%4f l=%4f\n" (t1-.t0) (t3-.t2)

;;

let bl,l = test_build ()
let () = test_scan bl l

let _ =
  let l = empty () in
  let l = rcons 10 l in
  let l = rcons 11 l in
  insert_after ((=) 10) 9 l;
  let l = rcons 12 l in
  let l = to_list @@ commit l in
  assert(l = [10;9;11;12])
;;

let _ =
  let l = empty () in
  let l = rcons 10 l in
  let l = rcons 11 l in
  insert_after ((=) 11) 9 l;
  let l = rcons 12 l in
  let l = to_list @@ commit l in
  assert(l = [10;11;9;12])
;;

let _ =
  let l = of_list [-2;-3] in
  let l = sort (-) l in
  let l = to_list l in
  assert(l = [-3;-2])
;;
