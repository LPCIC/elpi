(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* A purely functional sequence: the elements in [front], then those in [rear],
   a skew-binary random access list (Okasaki, Purely Functional Data Structures)
   turned around, so that the end where adding is cheap is the last one.

   [rear] is a list of complete binary trees, the most recent first, whose sizes
   strictly increase but for the first two, which can be equal. Adding an element
   either makes a new tree out of these two, or a new leaf. Hence cons and rcons
   are O(1) in the worst case, however a list is shared. *)

(* [Node (x, l, r)] holds the elements of [l], then the ones of [r], then [x] *)
type 'a tree = Leaf of 'a | Node of 'a * 'a tree * 'a tree
type 'a spine = Nil | Tree of int * 'a tree * 'a spine
type 'a t = { front : 'a list; rear : 'a spine }

let empty () = { front = []; rear = Nil }
let cons x l = { l with front = x :: l.front }

let snoc spine x =
  match spine with
  | Tree (w1, t1, Tree (w2, t2, rest)) when w1 = w2 -> Tree ((2 * w1) + 1, Node (x, t2, t1), rest)
  | s -> Tree (1, Leaf x, s)

let rcons x l = { l with rear = snoc l.rear x }

(* What is left to visit, from a tree: unless it is empty it starts with Emit, so
   that the next element is at hand *)
type 'a stack = Done | Emit of 'a * 'a stack | Visit of 'a tree * 'a stack
type 'a scan = 'a list * 'a stack

let rec push t k =
  match t with
  | Leaf x -> Emit (x, k)
  | Node (x, l, r) -> push l (Visit (r, Emit (x, k)))

let normalize = function Visit (t, k) -> push t k | k -> k

let stack_of_spine s =
  let rec aux k = function Nil -> k | Tree (_, t, s) -> aux (Visit (t, k)) s in
  normalize (aux Done s)

let to_scan { front; rear } = (front, stack_of_spine rear)
let is_empty = function [], Done -> true | _ -> false

let next = function
  | x :: xs, k -> (x, (xs, k))
  | [], Emit (x, k) -> (x, ([], normalize k))
  | [], (Done | Visit _) -> assert false

let to_list s =
  let rec aux acc s =
    if is_empty s then List.rev acc
    else
      let x, s = next s in
      aux (x :: acc) s
  in
  aux [] s

let of_list l = (l, Done)

let length s =
  let rec aux n s = if is_empty s then n else aux (n + 1) (snd (next s)) in
  aux 0 s

(* [at y ys] is the replacement of the list [y :: ys], if it has to change. *)
let edit_list at l =
  let rec aux acc = function
    | [] -> None
    | y :: ys -> (
        match at y ys with
        | Some l -> Some (List.rev_append acc l)
        | None -> aux (y :: acc) ys)
  in
  aux [] l

(* The trees older than the first element to change are shared *)
let rec edit_spine at = function
  | Nil -> None
  | Tree (_, t, older) -> (
      let elements () = to_list ([], normalize (Visit (t, Done))) in
      match edit_spine at older with
      | Some older -> Some (List.fold_left snoc older (elements ()))
      | None -> Option.map (List.fold_left snoc older) (edit_list at (elements ())))

let edit at l =
  match edit_list at l.front with
  | Some front -> Some { l with front }
  | None -> Option.map (fun rear -> { l with rear }) (edit_spine at l.rear)

let replace f x l =
  let at y ys = if f y then Some (x :: ys) else None in
  Option.value (edit at l) ~default:l

let remove f l =
  let at y ys = if f y then Some ys else None in
  Option.value (edit at l) ~default:l

let insert f x l =
  let at y ys = if f y > 0 then Some (x :: y :: ys) else None in
  match edit_list at l.front with
  | Some front -> { l with front }
  | None -> (
      let before_rear =
        match stack_of_spine l.rear with
        | Emit (y, _) -> f y > 0
        | Done | Visit _ -> false
      in
      if before_rear then { l with front = List.rev_append (List.rev l.front) [ x ] }
      else
        match edit_spine at l.rear with
        | Some rear -> { l with rear }
        | None -> rcons x l)

let pp pp_elt fmt l =
  let pp_sep fmt () = Format.fprintf fmt ";@ " in
  Format.fprintf fmt "@[<hov 2>[%a]@]" (Format.pp_print_list ~pp_sep pp_elt) (to_list (to_scan l))

let show pp_elt l = Format.asprintf "%a" (pp pp_elt) l
