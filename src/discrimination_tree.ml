(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
let arity_bits = 4
let k_bits = 2

(* value , arity, k *)
let kConstant = 0 (* (constant << arity_bits) lor arity *)
let kPrimitive = 1 (*Elpi_util.Util.CData.t hash *)
let kVariable = 2
let kOther = 3
let k_lshift = Sys.int_size - k_bits
let ka_lshift = Sys.int_size - k_bits - arity_bits
let k_mask = ((1 lsl k_bits) - 1) lsl k_lshift
let arity_mask = (((1 lsl arity_bits) lsl k_bits) - 1) lsl ka_lshift
let data_mask = (1 lsl ka_lshift) - 1
let encode k c a = (k lsl k_lshift) lor (a lsl ka_lshift) lor (c land data_mask)
let k_of n = (n land k_mask) lsr k_lshift

let arity_of n =
  let k = k_of n in
  if k == kConstant then (n land arity_mask) lsr ka_lshift else 0

let mkConstant c a = encode kConstant c a
let mkVariable = encode kVariable 0 0
let mkOther = encode kOther 0 0
let mkPrimitive c = encode kPrimitive (Elpi_util.Util.CData.hash c lsl k_bits) 0

let () = assert(k_of (mkConstant ~-17 0) == kConstant)
let () = assert(k_of mkVariable == kVariable)
let () = assert(k_of mkOther == kOther)

let isVariable x = k_of x == kVariable
let isOther x = k_of x == kOther

type cell = int
let pp_cell fmt n =
  let k = k_of n in
  if k == kConstant then
    let data = data_mask land n in
    let arity = (arity_mask land n) lsr ka_lshift in
    Format.fprintf fmt "Constant(%d,%d)" data arity
  else if k == kVariable then Format.fprintf fmt "Variable"
  else if k == kOther then Format.fprintf fmt "Other"
  else if k == kPrimitive then Format.fprintf fmt "Primitive"
  else Format.fprintf fmt "%o" k

let show_cell n =
  Format.asprintf "%a" pp_cell n

module Trie = struct
  (*
   * Trie: maps over lists.
   * Copyright (C) 2000 Jean-Christophe FILLIATRE
   * 
   * This software is free software; you can redistribute it and/or
   * modify it under the terms of the GNU Library General Public
   * License version 2, as published by the Free Software Foundation.
   * 
   * This software is distributed in the hope that it will be useful,
   * but WITHOUT ANY WARRANTY; without even the implied warranty of
   * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
   * 
   * See the GNU Library General Public License version 2 for more details
   * (enclosed in the file LGPL).
   *)

  (*s A trie is a tree-like structure to implement dictionaries over
      keys which have list-like structures. The idea is that each node
      branches on an element of the list and stores the value associated
      to the path from the root, if any. Therefore, a trie can be
      defined as soon as a map over the elements of the list is
      given. *)

  (*s Then a trie is just a tree-like structure, where a possible
      information is stored at the node (['a option]) and where the sons
      are given by a map from type [key] to sub-tries, so of type
      ['a t Ptmap.t]. The empty trie is just the empty map. *)

  type key = int list

  type 'a t =
    | Node of { data : 'a list; other : 'a t option; map : 'a t Ptmap.t }

  let empty = Node { data = []; other = None; map = Ptmap.empty }

  (*s To find a mapping in a trie is easy: when all the elements of the
      key have been read, we just inspect the optional info at the
      current node; otherwise, we descend in the appropriate sub-trie
      using [Ptmap.find]. *)

  let rec find l t =
    match (l, t) with
    | [], Node { data = [] } -> raise Not_found
    | [], Node { data } -> data
    | x :: r, Node { map } -> find r (Ptmap.find x map)

  let mem l t = try Fun.const true (find l t) with Not_found -> false

  (*s Insertion is more subtle. When the final node is reached, we just
      put the information ([Some v]). Otherwise, we have to insert the
      binding in the appropriate sub-trie [t']. But it may not exists,
      and in that case [t'] is bound to an empty trie. Then we get a new
      sub-trie [t''] by a recursive insertion and we modify the
      branching, so that it now points to [t''], with [Ptmap.add]. *)

  let add l v t =
    let rec ins = function
      | [], Node ({ data } as t) -> Node { t with data = v :: data }
      | x :: r, Node ({ other } as t) when isVariable x || isOther x ->
          let t' = match other with None -> empty | Some x -> x in
          let t'' = ins (r, t') in
          Node { t with other = Some t'' }
      | x :: r, Node ({ map } as t) ->
          let t' = try Ptmap.find x map with Not_found -> empty in
          let t'' = ins (r, t') in
          Node { t with map = Ptmap.add x t'' map }
    in
    ins (l, t)

  let rec pp (ppelem : Format.formatter -> 'a -> unit) (fmt : Format.formatter)
      (Node { data; other; map } : 'a t) : unit =
    Format.fprintf fmt "[values:{";
    Elpi_util.Util.pplist ppelem "; " fmt data;
    Format.fprintf fmt "} other:{";
    (match other with None -> () | Some m -> pp ppelem fmt m);
    Format.fprintf fmt "} key:{";
    Ptmap.to_list map |> Elpi_util.Util.pplist (fun fmt (k,v) -> pp_cell fmt k; pp ppelem fmt v) "; " fmt;
    Format.fprintf fmt "}]"

  let show (fmt : Format.formatter -> 'a -> unit) (n : 'a t) : string =
    let b = Buffer.create 22 in
    Format.fprintf (Format.formatter_of_buffer b) "@[%a@]" (pp fmt) n;
    Buffer.contents b
end

type path = cell list [@@deriving show]

let compare x y = x - y

let skip (path : path) : path =
  let rec aux arity path =
    if arity = 0 then path
    else
      match path with
      | [] -> assert false
      | m :: tl -> aux (arity - 1 + arity_of m) tl
  in
  match path with
  | [] -> Elpi_util.Util.anomaly "Skipping empty path is not possible"
  | hd :: tl -> aux (arity_of hd) tl

type 'a t = ('a * int) Trie.t

let pp pp_a fmt (t : 'a t) : unit = Trie.pp (fun fmt (a, _) -> pp_a fmt a) fmt t
let show pp_a (t : 'a t) : string = Trie.show (fun fmt (a, _) -> pp_a fmt a) t
let empty = Trie.empty
let index tree ps info ~time = Trie.add ps (info, time) tree

let in_index tree ps test =
  try
    let ps_set = Trie.find ps tree in
    List.exists (fun (x, _) -> test x) ps_set
  with Not_found -> false

(* the equivalent of skip, but on the index, thus the list of trees
    that are rooted just after the term represented by the tree root
    are returned (we are skipping the root) *)
let all_children other map =
  let rec get n = function
    | Trie.Node { other = None; map } as tree ->
        if n = 0 then [ tree ]
        else Ptmap.fold (fun k v res -> get (n - 1 + arity_of k) v @ res) map []
    | Trie.Node { other = Some other; map } as tree ->
        if n = 0 then [ tree; other ]
        else
          Ptmap.fold
            (fun k v res -> get (n - 1 + arity_of k) v @ res)
            map [ other ]
  in

  Ptmap.fold
    (fun k v res -> get (arity_of k) v @ res)
    map
    (match other with Some x -> [ x ] | None -> [])

(* NOTE: l1 and l2 are supposed to be sorted *)
let rec merge (l1 : ('a * int) list) l2 =
  match (l1, l2) with
  | [], l | l, [] -> l
  | ((_, tx) as x) :: xs, (_, ty) :: _ when tx > ty -> x :: merge xs l2
  | _, y :: ys -> y :: merge l1 ys

let get_all_children v mode = isOther v || (isVariable v && Elpi_util.Util.Output == mode)

(* get_all_children returns if a key should be unified with all the values of
   the current sub-tree. This key should be either K.to_unfy or K.variable.
   In the latter case, the mode boolean to be true (we are in output mode). *)
let rec retrieve_aux mode path = function
  | [] -> []
  | hd :: tl -> merge (retrieve mode path hd) (retrieve_aux mode path tl)

and retrieve mode path tree =
  match (tree, path) with
  | Trie.Node { data }, [] -> data
  | Trie.Node { other; map }, v :: path when get_all_children v mode ->
      retrieve_aux mode path (all_children other map)
  | Trie.Node { other = None; map }, node :: sub_path ->
      if mode == Elpi_util.Util.Input && isVariable node then []
      else
        let subtree = try Ptmap.find node map with Not_found -> Trie.empty in
        retrieve mode sub_path subtree
  | Trie.Node { other = Some other; map }, (node :: sub_path as path) ->
      merge
        (if mode == Elpi_util.Util.Input && isVariable node then []
        else
          let subtree = try Ptmap.find node map with Not_found -> Trie.empty in
          retrieve mode sub_path subtree)
        (retrieve mode (skip path) other)

let retrieve mode path index = retrieve mode path index |> List.map fst
