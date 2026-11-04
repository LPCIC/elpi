open Elpi_runtime.Bl
let size = min (Sys.max_array_length / 2 - 1) 9999999
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

let test_shared_list () =
  let build n = let rec aux i acc = if i > n then acc else aux (i+1) (rcons i acc) in aux 1 (empty ()) in
  let n = 65536 in
  let base = build n in
  let contents l = to_list (to_scan l) in
  let expected = contents base in

  (* extensions of the same list do not see each other *)
  let child1 = rcons 1 (rcons 2 base) in
  let child2 = rcons 3 base in
  let child3 = insert (fun x -> compare x 1) 4 base in
  assert (contents child1 = expected @ [2; 1]);
  assert (contents child2 = expected @ [3]);
  assert (contents child3 = 1 :: 4 :: List.tl expected);
  assert (contents base = expected);

  (* the cost of an extension does not depend on the size of the list *)
  let t0 = Gc.allocated_bytes () in
  for i = 1 to 1000 do ignore (Sys.opaque_identity (rcons i base)) done;
  assert (Gc.allocated_bytes () -. t0 < float_of_int (n * Sys.word_size / 8))
;;

let _ = test_shared_list ()

(* all the operations against a plain list, sharing the previous versions *)
let test_against_list () =
  Random.init 42;
  let rec ins x = function [] -> [x] | y :: ys when y > x -> x :: y :: ys | y :: ys -> y :: ins x ys in
  let rec rm x = function [] -> [] | y :: ys when y = x -> ys | y :: ys -> y :: rm x ys in
  let rec rep x = function [] -> [] | y :: ys when y = x -> (-x) :: ys | y :: ys -> y :: rep x ys in
  for _ = 1 to 100 do
    let pool = Array.make 8 (empty (), []) in
    for _ = 1 to 500 do
      let b, l = pool.(Random.int 8) in
      let x = Random.int 300 in
      let v =
        match Random.int 7 with
        | 0 -> insert (fun y -> compare y x) x b, ins x l
        | 1 -> remove (fun y -> y = x) b, rm x l
        | 2 -> replace (fun y -> y = x) (-x) b, rep x l
        | 3 -> cons x b, x :: l
        | _ -> rcons x b, l @ [x] in
      assert (to_list (to_scan (fst v)) = snd v);
      assert (length (to_scan (fst v)) = List.length (snd v));
      pool.(Random.int 8) <- v
    done
  done
;;

let _ = test_against_list ()

(* edits allocate in proportion to what follows the edited element, and
   nothing when no element matches *)
let test_edit_cost () =
  let build n = let rec aux i acc = if i > n then acc else aux (i+1) (rcons i acc) in aux 1 (empty ()) in
  let n = 65536 in
  let base = build n in
  let allocated f =
    let t0 = Gc.allocated_bytes () in
    for _ = 1 to 100 do ignore (Sys.opaque_identity (f ())) done;
    Gc.allocated_bytes () -. t0 in
  let small = float_of_int (n * Sys.word_size / 8) in
  assert (allocated (fun () -> remove (fun x -> x = 0) base) < small /. 64.);
  assert (allocated (fun () -> replace (fun x -> x = 0) 0 base) < small /. 64.);
  assert (allocated (fun () -> insert (fun x -> Int.compare x (n + 1)) 0 base) < small);
  assert (allocated (fun () -> replace (fun x -> x = n - 5) 0 base) < small);
  assert (allocated (fun () -> remove (fun x -> x = n - 5) base) < small);
  assert (allocated (fun () -> insert (fun x -> Int.compare x (n - 5)) 0 base) < small);
  let contents l = to_list (to_scan l) in
  let expected = contents base in
  assert (contents (replace (fun x -> x = n - 5) 0 base) = List.map (fun x -> if x = n - 5 then 0 else x) expected);
  assert (contents base = expected)
;;

let _ = test_edit_cost ()
