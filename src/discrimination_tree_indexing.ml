type term = Data.term
type constant = Data.constant

module TreeIndexable : Discrimination_tree.Indexable with 
  type input = term and type constant_name = constant
= struct
  type input = term
  type constant_name = constant 

  let compare = compare
  
  let rec path_string_of = function
    | Data.App (hd, x, xs) -> 
        let tl = List.map path_string_of (x :: xs) |> List.flatten in 
        Discrimination_tree.Constant (hd, List.length xs + 1) :: tl 
    | _ -> [Variable]
end

module DT = Discrimination_tree.Make(TreeIndexable)(Set.Make(Int)) 