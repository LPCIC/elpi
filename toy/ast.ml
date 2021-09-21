type tm =
  | App of string * tm list
  | Var of tm ref
  | Arg of int
