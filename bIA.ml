(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

module type S = sig
type 'a t

val init : int -> (int -> 'a) -> 'a t
val of_array : 'a array -> 'a t

val get : int -> 'a t -> 'a
val len : 'a t -> int
val sub : int -> int -> 'a t -> 'a t
val tl : 'a t -> 'a t

val map : ('a -> 'a) -> 'a t -> 'a t
val mapi : (int -> 'a -> 'a) -> 'a t -> 'a t

val fold_map : ('a -> 'b -> 'a * 'b) -> 'a t -> 'b -> 'a t * 'b
val fold_mapi : (int -> 'a -> 'b -> 'a * 'b) -> 'a t -> 'b -> 'a t * 'b

val fold : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
val foldi : (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

val fold2 : ('a -> 'c -> 'b -> 'b) -> 'a t -> 'c t -> 'b -> 'b
val fold2i : (int -> 'a -> 'c -> 'b -> 'b) -> 'a t -> 'c t -> 'b -> 'b

val for_all : ('a -> bool) -> 'a t -> bool
val for_alli : (int -> 'a -> bool) -> 'a t -> bool

val for_all2 : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool
val for_all2i : (int -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool

val filter : ('a -> bool) -> 'a t -> 'a t

val to_list : 'a t -> 'a list
val of_list : 'a list -> 'a t
end

type 'a t = int * int * 'a array
let init len f = 0, len, Array.init len f
let get i (start,stop,a) = assert(start + i < stop); a.(start + i)
let len (start,stop,_) = stop - start
let sub i len (start,stop,v) =
  if len > stop - start then raise (Invalid_argument "sub")
  else (start+i,start+i+len,v)
let tl (start,stop,v) = assert(stop - start > 0); (start+1,stop,v)
let of_array v = 0,Array.length v,v

let fold_mapi f (start,stop,ar as orig) acc =
  let len = stop-start in
  let i = ref start in
  let go_on = ref true in
  let temp = ref None in
  let r = ref acc in
  while !go_on && (!i < stop) do
    let v = ar.(!i) in
    let v', acc = f (!i - start) v !r in
    r := acc;
    if v == v' then incr i
    else begin
      go_on := false;
      temp := Some v';
    end
  done;
  if !i < stop then begin (* The array is not the same as the original one *)
    let ans = Array.sub ar start len in
    let v = match !temp with None -> assert false | Some x -> x in
    ans.(!i) <- v;
    incr i;
    while !i < stop do
      let v = ar.(!i) in
      let newpos = !i - start in
      let v', acc = f newpos v !r in
      r := acc;
      ans.(newpos) <- v';
      incr i
    done;
    (0,len,ans), !r
  end else
    orig, !r

let fmapi_fmap f = (); fun _ v a -> f v a
let fold_map f v acc = fold_mapi (fmapi_fmap f) v acc

let mapi f v = fst (fold_mapi (fun i x () -> f i x, ()) v ())
let map f v = fst (fold_map (fun x () -> f x, ()) v ())

let foldi f (start,stop,a) v =
  let rec aux i acc = if i = stop then acc else
    aux (i+1) (f (i-start) a.(i) acc) in
  aux start v

let foldi_fold f = (); fun _ v a -> f v a
let fold f a v = foldi (foldi_fold f) a v

let fold2i f (s1,e1,v1)  (s2,e2,v2) v =
  let off = s2 - s1 in
  let rec aux i acc = if i = e1 then acc else
    aux (i+1) (f (i-s1) v1.(i) v2.(i+off) acc) in
  aux s1 v

let fold2i_fold2 f = (); fun _ v1 v2 a -> f v1 v2 a
let fold2 f v1 v2 a = fold2i (fold2i_fold2 f) v1 v2 a

let for_alli f (s1,e1,v1) =
  let rec aux i = if i = e1 then true else
    f (i-s1) v1.(i) && aux (i+1)
  in
  aux s1

let alli_all f = (); fun _ x -> f x
let for_all f v = for_alli (alli_all f) v

let for_all2i f (s1,e1,v1) (s2,e2,v2) =
  let off = s2 - s1 in
  let rec aux i = if i = e1 then true else
    f (i-s1) v1.(i) v2.(i+off)
    && aux (i+1)
  in
  e1 - s1 = e2 - s2 && aux s1

let all2i_all2 f = (); fun _ x y -> f x y
let for_all2 f v1 v2 = for_all2i (all2i_all2 f) v1 v2

let to_list (start,stop,v) =
  let rec aux n acc = if n < start then acc else aux (n-1) (v.(n)::acc) in
  aux (stop-1) []

let of_list l =
  let len = List.length l in
  if len = 0 then raise (Invalid_argument "of_list");
  let v = Array.create len (List.hd l) in
  let _ = List.fold_left (fun i x -> v.(i) <- x; i+1) 0 l in
  0,len,v

let filter f (start,stop,v) =
  let a = Array.copy v in
  let cur = ref 0 in
  for i = start to stop - 1 do
    if f v.(i) then (a.(!cur) <- v.(i); incr cur)
  done;
  0,!cur,a
    
