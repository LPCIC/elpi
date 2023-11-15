(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module type IndexableTerm = sig
  type input
  
  type cell
  
  val show_cell: cell -> string
  val pp_cell: Format.formatter -> cell -> unit

  type path = cell list

  val compare: cell -> cell -> int
  val path_string_of : input -> path

  (* You have h(f(x,g(y,z)),t) whose path_string_of_term_with_jl is 
    (h,2).(f,2).(x,0).(g,2).(y,0).(z,0).(t,0) and you are at f and want to
    skip all its progeny, thus you want to reach t.

    You need to skip as many elements as the sum of all arieties contained
    in the progeny of f.

    The input ariety is the one of f while the path is x.g....t  
    Should be the equivalent of after_t in the literature (handbook A.R.)
  *)
  (* MAYBE: a pointer to t from f should increase performances (i.e. jump list from McCune 1990) *)
  val skip : path -> path
  val arity_of : cell -> int
  val variable : cell
end

module type DiscriminationTree =
    sig

      type input 
      type data
      type dataset
      type cell
      type t

      include Elpi_util.Util.Show with type t := t
      
      val iter : t -> (cell list -> dataset -> unit) -> unit
      val fold : t -> (cell list -> dataset -> 'b -> 'b) -> 'b -> 'b

      val empty : t
      val index : t -> input -> data -> t
      val remove_index : t -> input -> data -> t
      val in_index : t -> input -> (data -> bool) -> bool
      val retrieve_generalizations : t -> input -> dataset
      val retrieve_unifiables : t -> input -> dataset

      module type Collector = sig
        type t
        val empty : t
        val union : t -> t -> t
        val inter : t -> t -> data list
        val to_list : t -> data list
      end
      module Collector : Collector
      val retrieve_generalizations_sorted : t -> input -> Collector.t
      val retrieve_unifiables_sorted : t -> input -> Collector.t
    end

module type MyList = sig
    type elt
    type t 
    include Elpi_util.Util.Show with type t := t
    val empty: t
    val is_empty: t -> bool
    val mem: elt -> t -> bool
    val add: elt -> t -> t
    val singleton: elt -> t
    val remove: elt -> t -> t
    val union: t -> t -> t
    val compare: t -> t -> int
    val equal: t -> t -> bool
    val exists: (elt -> bool) -> t -> bool
    val elements: t -> elt list
    val find: elt -> t -> elt
    val of_list: elt list -> t
end

module Make (I:IndexableTerm) (A:MyList) : DiscriminationTree with 
type data = A.elt and type dataset = A.t and type input = I.input and 
type cell = I.cell =

    struct

      module OrderedPathStringElement = struct
        type t = I.cell

        let show = I.show_cell
        let pp = I.pp_cell
        let compare = I.compare
      end

      type data = A.elt
      type dataset = A.t

      type input = I.input
      type cell = I.cell

      module PSMap = Elpi_util.Util.Map.Make(OrderedPathStringElement)

      module Trie = Trie.Make(PSMap)

      type t = dataset Trie.t [@@deriving show]

      let pp = Trie.pp A.pp
      let show = Trie.show A.pp

      let empty = Trie.empty

      let iter dt f = Trie.iter (fun p x -> f p x) dt

      let fold dt f = Trie.fold (fun p x -> f p x) dt

      let index tree term info =
        let ps = I.path_string_of term in
        let ps_set =
          try Trie.find ps tree with Not_found -> A.empty 
        in
        Trie.add ps (A.add info ps_set) tree

      let remove_index tree term info =
        let ps = I.path_string_of term in
        try
          let ps_set = A.remove info (Trie.find ps tree) in
          if A.is_empty ps_set then Trie.remove ps tree
          else Trie.add ps ps_set tree
        with Not_found -> tree

      let in_index tree term test =
        let ps = I.path_string_of term in
        try
          let ps_set = Trie.find ps tree in
          A.exists test ps_set
        with Not_found -> false

      (* the equivalent of skip, but on the index, thus the list of trees
         that are rooted just after the term represented by the tree root
         are returned (we are skipping the root) *)
      let skip_root (Trie.Node (_value, map)) =
        let rec get n = function Trie.Node (_v, m) as tree ->
          if n = 0 then [tree] else 
          PSMap.fold (fun k v res -> (get (n-1 + I.arity_of k) v) @ res) m []
        in
          PSMap.fold (fun k v res -> (get (I.arity_of k) v) @ res) map []

      let retrieve unif tree term =
        let path = I.path_string_of term in
        let rec retrieve path tree =
          match tree, path with
          | Trie.Node (Some s, _), [] -> s
          | Trie.Node (None, _), [] -> A.empty 
          | Trie.Node (_, _map), v::path when v = I.variable && unif ->
              List.fold_left A.union A.empty
                (List.map (retrieve path) (skip_root tree))
          | Trie.Node (_, map), node::path ->
              A.union
                 (if not unif && I.variable = node then A.empty else
                  try retrieve path (PSMap.find node map)
                  with Not_found -> A.empty)
                 (try
                    match PSMap.find I.variable map, I.skip (node :: path) with
                    | Trie.Node (Some s, _), [] -> s
                    | n, path -> retrieve path n
                  with Not_found -> A.empty)
       in
        retrieve path tree
      

      let retrieve_generalizations tree term = retrieve false tree term
      let retrieve_unifiables tree term = retrieve true tree term

      module O = struct
        type t = A.t * int
        let compare (sa,wa) (sb,wb) = 
          let c = compare wb wa in
          if c <> 0 then c else A.compare sb sa
      end
      module S = Set.Make(O)

      (* TASSI: here we should think of a smarted data structure *)
      module type Collector = sig
        type t
        val empty : t
        val union : t -> t -> t
        val inter : t -> t -> data list
        val to_list : t -> data list
      end
      module Collector : Collector with type t = S.t = struct
        type t = S.t
        let union = S.union
        let empty = S.empty

        let merge l = 
          let rec aux s w = function
            | [] -> [s,w]
            | (t, wt)::tl when w = wt -> aux (A.union s t) w tl
            | (t, wt)::tl -> (s, w) :: aux t wt tl
          in
          match l with
          | [] -> []
          | (s, w) :: l -> aux s w l
          
        let rec undup ~eq = function
          | [] -> []
          | x :: tl -> x :: undup ~eq (List.filter (fun y -> not(eq x y)) tl)

        let to_list t =
          undup ~eq:(fun x y -> A.equal (A.singleton x) (A.singleton y)) 
            (List.flatten (List.map 
              (fun (x,_) -> A.elements x) (merge (S.elements t))))

        let rec filter_map f = function
          | [] -> []
          | x :: xs ->
              match f x with
              | None -> filter_map f xs
              | Some y -> y :: filter_map f xs

        let inter t1 t2 =
          let l1 = merge (S.elements t1) in
          let l2 = merge (S.elements t2) in
          let res = 
           List.flatten
            (List.map
              (fun (s, w) ->
                 filter_map (fun x ->
                   try Some (x, w + snd (List.find (fun (s,_w) -> A.mem x s) l2))
                   with Not_found -> None)
                   (A.elements s))
              l1)
          in
          undup ~eq:(fun x y -> A.equal (A.singleton x) (A.singleton y)) 
            (List.map fst (List.sort (fun (_,x) (_,y) -> y - x) res))
      end

      let retrieve_sorted unif tree term =
        let path = I.path_string_of term in
        let rec retrieve n path tree =
          match tree, path with
          | Trie.Node (Some s, _), [] -> S.singleton (s, n)
          | Trie.Node (None, _), [] -> S.empty
          | Trie.Node (_, _map), v::path when unif && v = I.variable ->
              List.fold_left S.union S.empty
                (List.map (retrieve n path) (skip_root tree))
          | Trie.Node (_, map), node::path ->
              S.union
                 (if not unif && node = I.variable then S.empty else
                  try retrieve (n+1) path (PSMap.find node map)
                  with Not_found -> S.empty)
                 (try
                    match PSMap.find I.variable map,I.skip (node::path) with
                    | Trie.Node (Some s, _), [] -> 
                       S.singleton (s, n)
                    | no, path -> retrieve n path no
                  with Not_found -> S.empty)
       in
        retrieve 0 path tree
      

      let retrieve_generalizations_sorted tree term = 
        retrieve_sorted false tree term
      let retrieve_unifiables_sorted tree term = 
        retrieve_sorted true tree term
end


