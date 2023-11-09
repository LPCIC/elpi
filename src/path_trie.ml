type 'a path_string_elem = 
  | Constant of 'a * int
  | Variable
  
type 'a path = ('a path_string_elem) 

module Indexable = struct 
  type c
  type t = c path 
end

module OrderedPath = struct
  type t = Indexable.t
  let compare = compare
end

module Dummy = Map.Make(OrderedPath)
module PathTrie = Trie.Make(Dummy)