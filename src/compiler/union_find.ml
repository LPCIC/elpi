open Elpi_util

module type M = sig
  include Hashtbl.HashedType

  val pp : Format.formatter -> t -> unit
  val compare : t -> t -> int
end

module Make (M : M) = struct
  module HT = struct
    module Hashtbl = Hashtbl.Make (M)

    type uf = { mutable rank : int; id : M.t; mutable parent : uf }
    type opened = uf Hashtbl.t
    type closed = opened

    let is_root t = t == t.parent
    let roots tbl = Hashtbl.fold (fun _ e acc -> if is_root e then e.id :: acc else acc) tbl []
    let rec to_list t = if is_root t then [ t.id ] else t.id :: to_list t.parent
    let create () = Hashtbl.create 2024

    let add tbl id =
      if not (Hashtbl.mem tbl id) then
        let rec cell = { rank = 0; id; parent = cell } in
        Hashtbl.add tbl id cell

    let find tbl key =
      let t = Hashtbl.find tbl key in
      let rec aux t =
        if is_root t then t
        else (
          t.parent <- t.parent.parent;
          aux t.parent)
      in
      aux t

    let union tbl (v1, v2) =
      let x = find tbl v1 in
      let y = find tbl v2 in
      if x == y then ()
      else
        let x, y = if x.rank < y.rank then (y, x) else (x, y) in
        y.parent <- x;
        if x.rank = y.rank then x.rank <- x.rank + 1

    let find tbl key = (find tbl key).id

    let rec clone uf =
      let cell = { rank = uf.rank; parent = uf.parent; id = uf.id } in
      let parent = if is_root uf then cell else clone uf.parent in
      cell.parent <- parent;
      cell

    let do_open tbl =
      Hashtbl.fold
        (fun k v acc ->
          Hashtbl.replace acc k (clone v);
          acc)
        tbl (create ())

    let merge tbl1 tbl2 =
      let tbl1 = do_open tbl1 in
      Hashtbl.iter (fun k v -> Hashtbl.replace tbl1 k (clone v)) tbl2;
      tbl1
  end

  module Map = struct
    module Hashtbl = Map.Make (M)

    type uf = { mutable rank : int; id : M.t; mutable parent : uf }
    type opened = uf Hashtbl.t
    type closed = opened

    let is_root t = t == t.parent
    let roots tbl = Hashtbl.fold (fun _ e acc -> if is_root e then e.id :: acc else acc) tbl []
    let rec to_list t = if is_root t then [ t.id ] else t.id :: to_list t.parent
    let create () = Hashtbl.empty

    let add tbl id =
      if not (Hashtbl.mem id tbl) then
        let rec cell = { rank = 0; id; parent = cell } in
        Hashtbl.add id cell tbl
      else tbl

    let find tbl key =
      let t = Hashtbl.find tbl key in
      let rec aux t =
        if is_root t then t
        else (
          t.parent <- t.parent.parent;
          aux t.parent)
      in
      aux t

    let union tbl (v1, v2) =
      let x = find tbl v1 in
      let y = find tbl v2 in
      if x == y then ()
      else
        let x, y = if x.rank < y.rank then (y, x) else (x, y) in
        y.parent <- x;
        if x.rank = y.rank then x.rank <- x.rank + 1

    let find tbl key = (find tbl key).id

    let rec clone uf =
      let cell = { rank = uf.rank; parent = uf.parent; id = uf.id } in
      let parent = if is_root uf then cell else clone uf.parent in
      cell.parent <- parent;
      cell

    let do_open tbl =
      Hashtbl.fold
        (fun k v acc ->
          Hashtbl.add  k (clone v) acc)
        tbl (create ())

    let merge tbl1 tbl2 =
      let tbl1 = do_open tbl1 in
      Hashtbl.fold (fun k v acc -> Hashtbl.add k (clone v) acc) tbl2 tbl1
  end

  include HT

  let do_close a = a

  (* printers *)
  let pp_uf fmt t = Format.fprintf fmt "%a" (Util.pplist M.pp ",") (to_list t)

  let pp fmt tbl =
    let keys = Hashtbl.to_seq tbl in
    let l = List.of_seq keys in
    let sorted_keys = List.sort (fun a b -> compare (fst a) (fst b)) l in
    let pp_elt fmt (k, v) =
      if is_root v then Format.fprintf fmt "@[@[%a@] -> root;" M.pp k
      else Format.fprintf fmt "@[@[%a@] -> @[%a@]@];" M.pp k pp_uf v.parent
    in
    Format.fprintf fmt "{{ %a }}" (Util.pplist pp_elt ",") sorted_keys

  let show t = Format.asprintf "%a" pp t
  let pp_closed = pp
  let show_closed = show
  let pp_opened = pp
  let show_opened = show
  let create_close = create
  let union_c = union
end
