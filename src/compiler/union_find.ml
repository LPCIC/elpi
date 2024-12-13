(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util

module type S = sig
  include Util.Show
  include Util.ShowKey

  val empty : t
  val is_empty : t -> bool
  val find : t -> key -> key
  val union : t -> key -> key -> key option * t
  val merge : t -> t -> t
  val roots : t -> key list
end

module Make (M : Elpi_util.Util.Map.S) : S with type t = M.key M.t and type key = M.key = struct
  type key = M.key [@@deriving show]
  type t = key M.t [@@deriving show]

  let empty = M.empty
  let is_empty = ( = ) M.empty
  let rec find m v = 
    match M.find_opt v m with
    | None -> v
    | Some e -> find m e

  let union m i j =
    (* assert ( i <> j ); *)
    let ri = find m i in
    let rj = find m j in
    (* r1 is put in the same disjoint set of rj and can be removed from other
       data structures *)
    if ri <> rj then (Some ri, M.add ri rj m) else (None, m)

  let merge u1 u2 =
    (* all disjoint-set in u1 and u2 should be pairwise disjoint *)
    M.union (fun _ a _ -> Some a) u1 u2
  (* M.fold (fun k father acc ->
     let acc = if M.mem father acc then assert false else add acc father in
     union acc k father
     ) u1 u2 *)

  let is_root acc k = find acc k = k

  let roots d =
    let roots = ref [] in
    let add e = if not (List.mem e !roots) then roots := e :: !roots in
    M.iter (fun k v -> add (find d k)) d;
    !roots

  let pp fmt v =
    Format.fprintf fmt "{{\n";
    M.iter (fun k v -> if k <> v then Format.fprintf fmt "@[%a -> %a@]\n" M.pp_key k M.pp_key v) v;
    Format.fprintf fmt "}}@."

  let pp_key = M.pp_key
end
