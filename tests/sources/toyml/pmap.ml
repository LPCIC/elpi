module type T = sig
  type t
  val hash : t -> int
end

module Make(X : T) = struct
  module M = Map.Make(struct
    type t = int
    let compare x y = x - y
  end)
  type 'a t = (X.t * 'a) list M.t
  let empty = M.empty
  let add k v m =
    let h = X.hash k in
    try
      let l = M.find h m in
      let l = List.remove_assq k l in
      M.add h ((k,v) :: l) m
    with Not_found ->
      M.add h [k,v] m
  let find_opt k m =
    try
      let h = Hashtbl.hash k in
      let l = M.find h m in
      Some (List.assq k l)
    with Not_found -> None

end
