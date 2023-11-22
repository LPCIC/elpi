(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

let (=) (x:int) (y:int) = x = y
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

module Make (K : IndexableTerm) :
  DiscriminationTree with type key = K.cell and type keylist = K.path = struct
  module OrderedPathStringElement = struct
    type t = K.cell

    let show = K.show_cell
    let pp = K.pp_cell
    let compare = K.compare
  end

  module PSMap = Elpi_util.Util.Map.Make (OrderedPathStringElement)
  module Trie = Trie.Make (PSMap)

  type key = K.cell
  type keylist = K.path
  type 'a t = ('a * int) Trie.t

  let pp pp_a fmt (t : 'a t) : unit =
    Trie.pp (fun fmt (a, _) -> pp_a fmt a) fmt t

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
          else
            PSMap.fold (fun k v res -> get (n - 1 + K.arity_of k) v @ res) m []
    in
    PSMap.fold (fun k v res -> get (K.arity_of k) v @ res) map []

  (* NOTE: l1 and l2 are supposed to be sorted *)
  let rec merge (l1 : ('a * int) list) l2 =
    match (l1, l2) with
    | [], l | l, [] -> l
    | ((_, tx) as x) :: xs, (_, ty) :: _ when tx > ty -> x :: merge xs l2
    | _, y :: ys -> y :: merge l1 ys

  let retrieve unif tree path =
    let open Trie in
    (*
      to_unify returns if a key should be unified with all the values of
      the current sub-tree. This key should be either K.to_unfy or K.variable.
      In the latter case, the unif boolean to be true (we are in output mode).
    *)
    let to_unify v = v = K.to_unify || (v = K.variable && unif) in
    let rec retrieve_aux path = function
      | [] -> []
      | hd :: tl -> merge (retrieve path hd) (retrieve_aux path tl)
    and retrieve path tree =
      match (tree, path) with
      | Node (s, _), [] -> s
      | Node (_, _map), v :: path when false && to_unify v ->
        assert false;
          retrieve_aux path (skip_root tree)
      (* Note: in the following branch the head of the path can't be K.to_unify *)
      | Node (_, map), (node :: sub_path as path) ->
          let find_by_key key =
            try
              match (PSMap.find key map, K.skip path) with
              | Node (s, _), [] -> s
              | n, path -> retrieve path n
            with Not_found -> []
          in
          (*
          merge
            (merge
            *)
               (if (not unif) && K.variable = node then []
                else
                  let subtree =
                    try PSMap.find node map
                    with Not_found -> Node([],PSMap.empty)
                  in
                  retrieve sub_path subtree
                  )
                  (*
               (find_by_key K.variable))
            (find_by_key K.to_unify)
            *)
    in
    retrieve path tree

  let retrieve_generalizations tree term =
    retrieve false tree term |> List.map fst

  let retrieve_unifiables tree term = retrieve true tree term |> List.map fst
end
