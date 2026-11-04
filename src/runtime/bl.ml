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

(* An edit changes the first element [y] such that [test y] into the list
   [rewrite y ys], where [ys] are the elements after [y]. Searching allocates
   nothing: only the part that changes is turned into a list. *)

let rec tree_exists test = function
  | Leaf x -> test x
  | Node (x, l, r) -> tree_exists test l || tree_exists test r || test x

let tree_to_list t = to_list ([], normalize (Visit (t, Done)))

(* [test] holds on an element of [l] *)
let edit_list test rewrite l =
  let rec aux acc = function
    | [] -> assert false
    | y :: ys -> if test y then List.rev_append acc (rewrite y ys) else aux (y :: acc) ys
  in
  aux [] l

(* [edit_tree test rewrite w t older] adds to [older] the elements of [t], of
   size [w], edited. [test] holds on an element of [t]. The subtrees before
   that element are shared: they are smaller than the trees of [older], whose
   sizes strictly increase, so they can be put on top of it. *)
let rec edit_tree test rewrite w t older =
  match t with
  | Leaf y -> List.fold_left snoc older (rewrite y [])
  | Node (x, l, r) ->
      let w = (w - 1) / 2 in
      if tree_exists test l then
        let s = edit_tree test rewrite w l older in
        snoc (List.fold_left snoc s (tree_to_list r)) x
      else if tree_exists test r then snoc (edit_tree test rewrite w r (Tree (w, l, older))) x
      else List.fold_left snoc (Tree (w, r, Tree (w, l, older))) (rewrite x [])

(* The trees older than the first element to change are shared *)
let rec edit_spine test rewrite = function
  | Nil -> None
  | Tree (w, t, older) -> (
      match edit_spine test rewrite older with
      | Some older -> Some (List.fold_left snoc older (tree_to_list t))
      | None -> if tree_exists test t then Some (edit_tree test rewrite w t older) else None)

let edit test rewrite l =
  if List.exists test l.front then Some { l with front = edit_list test rewrite l.front }
  else Option.map (fun rear -> { l with rear }) (edit_spine test rewrite l.rear)

let replace f x l = Option.value (edit f (fun _ ys -> x :: ys) l) ~default:l
let remove f l = Option.value (edit f (fun _ ys -> ys) l) ~default:l

let insert f x l =
  let test y = f y > 0 in
  if List.exists test l.front then { l with front = edit_list test (fun y ys -> x :: y :: ys) l.front }
  else
    let before_rear = match stack_of_spine l.rear with Emit (y, _) -> test y | Done | Visit _ -> false in
    if before_rear then { l with front = l.front @ [ x ] }
    else
      match edit_spine test (fun y ys -> x :: y :: ys) l.rear with
      | Some rear -> { l with rear }
      | None -> rcons x l

let pp pp_elt fmt l =
  let pp_sep fmt () = Format.fprintf fmt ";@ " in
  Format.fprintf fmt "@[<hov 2>[%a]@]" (Format.pp_print_list ~pp_sep pp_elt) (to_list (to_scan l))

let show pp_elt l = Format.asprintf "%a" (pp pp_elt) l
