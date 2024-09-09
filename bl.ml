type 'a t = BNil | BCons of { head : 'a; mutable tail : 'a t }

type 'a builder = { mutable list : 'a t; mutable last : 'a t }

let empty : _ builder = { list = BNil; last = BNil }

let init b head = b.list <- BCons { head ; tail = BNil }; b.last <- b.list

let cons x = function
  | { list = BNil } as b -> init b x
  | { list } as b -> b.list <- BCons { head = x; tail = list }

let rcons x = function
  | { list = BNil } as b -> init b x
  | { last = BCons l } as b -> l.tail <- BCons { head = x; tail = BNil }; b.last <- l.tail
  | _ -> assert false


let test_build () =
  let size = 9999999 in
  Gc.minor (); Gc.major ();
  
  let t0 = Unix.gettimeofday () in
  let b = empty in
  for i = 0 to size do
    rcons i b;
  done;
  let r1 = b.list in
  let t1 = Unix.gettimeofday () in

  Gc.minor (); Gc.major ();

  let t2 = Unix.gettimeofday () in
  let rec aux n acc =
    if n = 0 then acc else aux (n-1) (n :: acc) in
  let r2 = List.rev @@ aux size [] in
  let t3 = Unix.gettimeofday () in

  Printf.eprintf "build: bl=%4f l=%4f\n" (t1-.t0) (t3-.t2);
  r1, r2
;;

let test_scan bl l =

  let rec aux = function
  | BCons { head; tail } -> assert(head >= 0); aux tail
  | BNil -> ()
in
  let t0 = Unix.gettimeofday () in
  aux bl;
  let t1 = Unix.gettimeofday () in

  let rec aux = function
  | head :: tail -> assert(head >= 0); aux tail
  | [] -> ()
  in

  let t2 = Unix.gettimeofday () in
  aux l;
  let t3 = Unix.gettimeofday () in

  Printf.eprintf "scan: bl=%4f l=%4f\n" (t1-.t0) (t3-.t2)

;;

let bl,l = test_build ()
let () = test_scan bl l

