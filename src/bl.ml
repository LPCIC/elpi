(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(*
build: bl=0.517913 l=0.583841        
scan: bl=0.025057 l=0.020488

base: 0.011125                       
extend: 1.322639
query: 0.000045
optimize: 0.000187
ok
exec: 0.000044
*)

module Array = struct

  type 'a t = 'a data ref

  and 'a data =
    | Array of 'a array
    | Diff of int * 'a * 'a t
    [@@deriving show]
  
  let empty () = ref @@ Array [||]

  let make n v =
    ref (Array (Array.make n v))
  
  let init n f =
    ref (Array (Array.init n f))
  
  (* `reroot t` ensures that `t` becomes an `Array` node.
      This is written in CPS to avoid any stack overflow. *)
  let rec rerootk t k = match !t with
    | Array _ -> k ()
    | Diff (i, v, t') ->
        rerootk t' (fun () ->
            (match !t' with
       | Array a as n ->
           let v' = a.(i) in
           a.(i) <- v;
           t := n;
           t' := Diff (i, v', t)
       | Diff _ -> assert false
            );
            k()
          )
  
  let reroot t = rerootk t (fun () -> ())

  let extend len t a =
    let data = reroot t; match ! t with Array x -> x | Diff _ -> assert false in
    let newdata = Array.make (2*(max 1 len)) a in
    if len > 0 then
      Array.blit data 0 newdata 0 len;
    ref @@ Array newdata

  let get t i =
    match !t with
    | Array a ->
        a.(i)
    | Diff _ ->
        reroot t;
        (match !t with Array a -> a.(i) | Diff _ -> assert false)
  
  let set t i v =
    reroot t;
    match !t with
    | Array a as n ->
        let old = a.(i) in
        if old == v then
    t
        else (
    a.(i) <- v;
    let res = ref n in
    t := Diff (i, old, res);
    res
        )
    | Diff _ ->
        assert false

  let shift_right t i len =
    let rec shift t j =
      if j < i then t
      else shift (set t (j+1) (get t j)) (j-1)
    in
      shift t (i+len-1)

  let shift_left t i len =
    let rec shift t j =
      if j = len-1 then t
      else shift (set t j (get t (j+1))) (j + 1)
    in
      shift t i

  let rec length t = match !t with Diff(_,_,x) -> length x | Array a -> Array.length a

  let of_list l = ref @@ Array (Array.of_list l)
end

type 'a t =
  | BArray of { len : int; data : 'a Array.t }
  | BCons of 'a * 'a t
  [@@deriving show]

  (* | UndoRcons of { old_tail : 'a data; next : 'a t }
  | UndoInsert of { old_before : 'a data; old_after : 'a data; next : 'a t } *)
(* and 'a t = 'a data ref *)

let pp_pointer fmt x = Format.fprintf fmt "%x" (Obj.magic x land 0xffffff)
(* let rec pp pp_a fmt = function
  | BArray -> Format.fprintf fmt "[]"
  | BCons { head; tail; last } as x ->
      Format.fprintf fmt "[self %a, tail %a, last %a] %a :: "
        pp_pointer x
        pp_pointer tail
        pp_pointer last
        pp_a head;
      pp pp_a fmt tail *)
  (* | UndoRcons { old_tail; next } -> Format.fprintf fmt "UndoRcons %a :: " pp_pointer old_tail ; pp pp_a fmt next
  | UndoInsert { old_before; old_after; next } -> Format.fprintf fmt "UndoInsert %a - %a :: " pp_pointer old_before pp_pointer old_after; pp pp_a fmt next *)

(* let show pp_a x = Format.asprintf "%a" (pp pp_a) x *)

let empty () = BArray { len = 0; data = Array.empty () }

let extendk len data a k =
  let newdata = Array.extend len data a in
  BArray { len = len + 1; data = k newdata }
let extend len data a = extendk len data a (fun x -> x)
  
let cons head tail = BCons(head,tail)

let rec rcons elt l =
  match l with
  | BCons(x,xs) -> BCons(x,rcons elt xs)
  | BArray { len; data } when len < Array.length data -> BArray { len = len + 1; data = Array.set data len elt }
  | BArray { len; data } -> extend len data elt

let rec replace f x = function
  | BCons (head,tail) when f head -> BCons(x,tail)
  | BCons (head, tail) -> BCons (head, replace f x tail)
  | BArray { len; data } as a ->
      let rec aux i =
        if i < len then
          if f data.(i) then BArray { len; data = Array.set data i x }
          else aux (i+1)
        else
          a
      in
        aux 0

let rec remove f = function
  | BCons (head,tail) when f head -> tail
  | BCons (head, tail) -> BCons (head, remove f tail)
  | BArray { len; data } as a ->
      let rec aux i =
        if i < len then
          if f data.(i) then BArray { len = len-1; data = Array.shift_left data i len }
          else aux (i+1)
        else 
          a
      in
        aux 0

let rec insert f x = function
  | BCons (head, tail) when f head <= 0 -> BCons (head, BCons(x,tail))
  | BCons (head, tail) -> BCons (head, insert f x tail)
  | BArray { len; data } ->
    let rec aux i =
      if i < len then
        if f data.(i) > 0 then
          if len < Array.length data then begin
            let data = Array.shift_right data i (len-i) in
            BArray { len = len + 1; data = Array.set data i x }
          end else
            extendk len data x (fun data ->
              let data = Array.shift_right data i (len-i) in
              Array.set data i x)
        else
          aux (i+1)
      else
          if len < Array.length data then begin
            BArray { len = len + 1; data = Array.set data len x }
          end else
            extendk len data x (fun data -> Array.set data len x)

    in
      aux 0
          
let rec commit = function
  | BCons(x,xs) -> x :: commit xs
  | BArray { len; data } ->
      let[@tail_mod_cons] rec aux i =
        if i = len then []
        else data.(i) :: aux (i+1)
      in
        aux 0

type 'a scan = 'a t * int
let to_scan x = x, 0
let is_empty (x,n) =
  match x with
  | BArray { len } -> len = n
  | BCons _ -> false

let next (x,n) =
  match x with
  | BArray { len; data } -> assert(n < len); data.(n), (x,n+1)
  | BCons (a,xs) -> a, (xs,n)

let to_list (x,n) =
  if n = 0 then commit x else
  match x with
  | BCons _ -> assert false
  | BArray { len; data } ->
    let[@tail_mod_cons] rec aux i =
      if i = len then []
      else data.(i) :: aux (i+1)
    in
    aux n

let of_list l = let data = Array.of_list l in BArray { len = Array.length data; data }, 0

let length (x,i) =
  let rec aux i = function
    | BCons (_,l) -> aux (i+1) l
    | BArray { len } -> i + len
  in
  aux (-i) x