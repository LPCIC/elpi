(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(*let (=) (x:int) (y:int) = x = y*)
module type IndexableTerm = sig
  type cell
  type path = cell list

  val show_cell : cell -> string
  val pp_cell : Format.formatter -> cell -> unit
  val compare : cell -> cell -> int

  (* You have h(f(x,g(y,z)),t) whose path_string_of_term_with_jl is
     (h,2).(f,2).(x,0).(g,2).(y,0).(z,0).(t,0) and you are at f and want to
     skip all its progeny, thus you want to reach t.

     You need to skip as many elements as the sum of all arieties contained
     in the progeny of f.

     The input ariety is the one of f while the path is x.g....t
     Should be the equivalent of after_t in the literature (handbook A.R.)
  *)
  (* MAYBE: a pointer to t from f should increase performances (i.e. jump list
            from McCune 1990) *)
  val skip : path -> path
  val arity_of : cell -> int
  val variable : cell
  val to_unify : cell
  val pp : Format.formatter -> path -> unit
  val show : path -> string
end

module type DiscriminationTree = sig
  type key
  type keylist = key list
  type 'a t

  include Elpi_util.Util.Show1 with type 'a t := 'a t

  val iter : 'a t -> (keylist -> 'a -> unit) -> unit
  val fold : 'a t -> (keylist -> 'a -> 'b -> 'b) -> 'b -> 'b
  val empty : 'a t
  val index : 'a t -> keylist -> 'a -> time:int -> 'a t
  val in_index : 'a t -> keylist -> ('a -> bool) -> bool
  val retrieve_generalizations : 'a t -> keylist -> 'a list
  val retrieve_unifiables : 'a t -> keylist -> 'a list
end

let arity_bits = 4
let k_bits = 2

(* value , arity, k *)
let kConstant = 0 (* (constant << arity_bits) lor arity *)
let kPrimitive = 1 (*Elpi_util.Util.CData.t hash *)
let kVariable = 2
let kOther = 3

let k_mask = (1 lsl k_bits) - 1
let arity_mask = ((1 lsl arity_bits) lsl k_bits) - 1
let k_of n = n land k_mask

let arity_of n =
  let k = k_of n in
  if k == kConstant then (n land arity_mask) lsr k_bits
  else 0
let encode k c a = ((c lsl arity_bits) lsl k_bits) lor (a lsl k_bits) lor k
let mask_low n = n land arity_mask


let mkConstant c a = encode kConstant c a
let mkVariable = kVariable
let mkOther = kOther
let mkPrimitive c = (Elpi_util.Util.CData.hash c lsl k_bits) lor kPrimitive

type cell = int [@@deriving show]
type path = cell list [@@deriving show]

let compare x y = x - y

let skip (path : path) : path =
  let rec aux arity path =
    if arity = 0 then path
    else
      match path with
      | [] -> assert false
      | m :: tl -> aux (arity - 1 + arity_of m) tl
  in
  match path with
  | [] -> Elpi_util.Util.anomaly "Skipping empty path is not possible"
  | hd :: tl -> aux (arity_of hd) tl

module PSMap = Elpi_util.Util.Map.Make (OrderedPathStringElement)
module Trie = Trie.Make (PSMap)

type 'a t = ('a * int) Trie.t

let pp pp_a fmt (t : 'a t) : unit = Trie.pp (fun fmt (a, _) -> pp_a fmt a) fmt t
let show pp_a (t : 'a t) : string = Trie.show (fun fmt (a, _) -> pp_a fmt a) t
let empty = Trie.empty
let iter dt f = Trie.iter (fun p (x, _) -> f p x) dt
let fold dt f = Trie.fold (fun p (x, _) -> f p x) dt
let index tree ps info ~time = Trie.add ps (info, time) tree

let in_index tree ps test =
  try
    let ps_set = Trie.find ps tree in
    List.exists (fun (x, _) -> test x) ps_set
  with Not_found -> false

(* the equivalent of skip, but on the index, thus the list of trees
    that are rooted just after the term represented by the tree root
    are returned (we are skipping the root) *)
let skip_root (Trie.Node (_value, map)) =
  let rec get n = function
    | Trie.Node (_v, m) as tree ->
        if n = 0 then [ tree ]
        else PSMap.fold (fun k v res -> get (n - 1 + arity_of k) v @ res) m []
  in
  PSMap.fold (fun k v res -> get (arity_of k) v @ res) map []

(* NOTE: l1 and l2 are supposed to be sorted *)
let rec merge (l1 : ('a * int) list) l2 =
  match (l1, l2) with
  | [], l | l, [] -> l
  | ((_, tx) as x) :: xs, (_, ty) :: _ when tx > ty -> x :: merge xs l2
  | _, y :: ys -> y :: merge l1 ys

let to_unify v unif = v == kOther || (v == kVariable && unif)

(*
      to_unify returns if a key should be unified with all the values of
      the current sub-tree. This key should be either K.to_unfy or K.variable.
      In the latter case, the unif boolean to be true (we are in output mode).
    *)
let rec retrieve_aux unif path = function
  | [] -> []
  | hd :: tl -> merge (retrieve unif path hd) (retrieve_aux unif path tl)

and retrieve unif path tree =
  match (tree, path) with
  | Trie.Node (s, _), [] -> s
  | Trie.Node (_, _map), v :: path when false && to_unify v unif ->
      assert false;
      retrieve_aux unif path (skip_root tree)
  (* Note: in the following branch the head of the path can't be K.to_unify *)
  | Trie.Node (_, map), (node :: sub_path as path) ->
      (*
          merge
            (merge
            *)
      if (not unif) && kVariable == node then []
      else
        let subtree =
          try PSMap.find node map with Not_found -> Node ([], PSMap.empty)
        in
        retrieve unif sub_path subtree
(*
               (find_by_key unif map path K.variable))
            (find_by_key unif map path K.to_unify)
            *)

and find_by_key unif key map path =
  try
    match (PSMap.find key map, skip path) with
    | Trie.Node (s, _), [] -> s
    | n, path -> retrieve unif path n
  with Not_found -> []

let retrieve_generalizations tree term =
  retrieve false term tree |> List.map fst

let retrieve_unifiables tree term = retrieve true term tree |> List.map fst
