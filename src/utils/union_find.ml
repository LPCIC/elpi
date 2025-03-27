(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

module type S = sig
  include Util.Show
  include Util.ShowKey
  module KeySet : Util.Set.S with type elt = key
  val empty : t
  val is_empty : t -> bool
  val find : t -> key -> key
  val find_class : t -> key -> key * KeySet.t
  val union : t -> key -> canon:key -> key option * t
  val merge : t -> t -> t
  val roots : t -> KeySet.t
  val mapi : (key -> key) -> t -> t
end

module Make (O : Util.Map.OrderedType) : S with type key = O.t = struct
  module M = Util.Map.Make(O)
  module KeySet = Util.Set.Make(O)
  type key = M.key [@@deriving show]
  type t = (key * KeySet.t) M.t [@@deriving show]

  let empty = M.empty
  let is_empty = ( = ) M.empty
  let rec find m v = 
    match M.find_opt v m with
    | None -> v
    | Some (e,_) -> find m e

    let rec find_class m v s = 
      match M.find_opt v m with
      | None -> v, KeySet.add v s
      | Some (e,s1) -> find_class m e (KeySet.add e (KeySet.union s1 s))

    let find_class m v = find_class m v KeySet.empty
  
  let union m i ~canon:j =
    (* assert ( i <> j ); *)
    let ri, si = find_class m i in
    let rj, sj = find_class m j in
    (* ri is put in the same disjoint set of rj and can be removed from other
       data structures *)
    if O.compare ri rj != 0 then (Some ri, M.add ri (rj,KeySet.union si sj) m) else (None, m)

  let merge u1 u2 =
    (* all disjoint-set in u1 and u2 should be pairwise disjoint *)
    M.union (fun _ (a,sa) (_,sb) -> Some (a,KeySet.union sa sb)) u1 u2
  (* M.fold (fun k father acc ->
     let acc = if M.mem father acc then assert false else add acc father in
     union acc k father
     ) u1 u2 *)

  let mapi f t =
    M.fold (fun k (v,s) acc -> M.add (f k) (f v,KeySet.map f s) acc) M.empty t

  let is_root acc k = O.compare (find acc k) k = 0

  let roots d =
    let roots = ref KeySet.empty in
    let add e = if not (KeySet.mem e !roots) then roots := KeySet.add e !roots in
    M.iter (fun k v -> add (find d k)) d;
    !roots

  let pp fmt v =
    Format.fprintf fmt "{{\n";
    M.iter (fun k (v,cl) -> if O.compare k v != 0 then Format.fprintf fmt "@[%a -> %a@]\n" M.pp_key k M.pp_key v) v;
    Format.fprintf fmt "}}@."

  let pp_key = M.pp_key
end
