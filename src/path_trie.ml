type 'a path_string_elem = 
  | Constant of 'a * int
  | Variable  
  
type 'a path = ('a path_string_elem) 

module Indexable = struct 
  type c = int
  type t = c path 
end

module OrderedPath = struct
  type t = Indexable.t
  let compare x y = match x, y with 
  | Variable, _ -> 0 
  | _, Variable -> 0 
  | a, b -> compare a b

  let print = function 
  | Constant (a, b) -> Printf.printf "Constant (%d, %d) " a b
  | Variable -> Printf.printf "Variable "
end

module Dummy = Map.Make(OrderedPath)
module PathTrie = struct 
  include Trie.Make(Dummy)

  let rec find_skip (t: 'a t) (depth: int) : 'a t list = 
    match t with 
    | Node (Some a, v) when depth = 0 -> 
        Printf.printf "In Node None when depth is 0 with length\n";
        Dummy.bindings v |> List.map snd
    | Node (_, tmap) ->
        let bindings = Dummy.bindings tmap in
        Printf.printf "bindings length in rec call %d\n" (List.length bindings); 
        let x = List.map (fun (k, v) -> 
          if depth = 0 then [v] else 
          match k with 
            | Variable -> 
              Printf.printf "In Variable with remaining depth %d\n" depth;
              find_skip v (depth - 1)
            | Constant (c, arity) -> 
              Printf.printf "In Constant with value %d\n" c;
              find_skip v (depth - 1 + arity)
          ) bindings in 
        List.flatten x


  let rec find1 l t : 'a list = 
    match (l, t) with 
    | [], Node (None, _) -> []
    | [], Node (Some v, _) -> [v]
    (* TODO: Next line, Dummy.find should return also variables *)
    | Constant (p,t) as c :: tl, Node (_, k) -> 
        find1 tl (Dummy.find c k)
    | Variable :: tl, Node (_, k) -> 
        let bindings = Dummy.bindings k in
        Printf.printf "bindings length is %d\n" (List.length bindings); 
        let elts = List.map (function 
          | Variable, x -> find1 tl x 
          | Constant (c, 0), x -> find1 tl x
          | Constant (c, depth), x -> 
              Printf.printf "The depth of %d is %d\n" c depth;
              let trees = find_skip x (depth - 1) in 
              Printf.printf "subtrees length is %d\n" (List.length trees); 
              let res = List.map (find1 tl) trees in 
              List.flatten res) bindings in
        List.flatten elts
end