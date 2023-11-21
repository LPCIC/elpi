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

module Make (M : Elpi_util.Util.Map.S) = struct
  (*s Then a trie is just a tree-like structure, where a possible
      information is stored at the node (['a option]) and where the sons
      are given by a map from type [key] to sub-tries, so of type
      ['a t M.t]. The empty trie is just the empty map. *)

  type key = M.key list

  type 'a t = Node of 'a list * 'a t M.t
  let empty = Node ([], M.empty)

  (*s To find a mapping in a trie is easy: when all the elements of the
      key have been read, we just inspect the optional info at the
      current node; otherwise, we descend in the appropriate sub-trie
      using [M.find]. *)

  let rec find l t =
    match (l, t) with
    | [], Node ([], _) -> raise Not_found
    | [], Node (v, _) -> v
    | x :: r, Node (_, m) -> find r (M.find x m)

  let mem l t = try Fun.const true (find l t) with Not_found -> false

  (*s Insertion is more subtle. When the final node is reached, we just
      put the information ([Some v]). Otherwise, we have to insert the
      binding in the appropriate sub-trie [t']. But it may not exists,
      and in that case [t'] is bound to an empty trie. Then we get a new
      sub-trie [t''] by a recursive insertion and we modify the
      branching, so that it now points to [t''], with [M.add]. *)

  let add l v t =
    let rec ins = function
      | [], Node (l, m) -> Node (v::l, m)
      | x :: r, Node (v, m) ->
          let t' = try M.find x m with Not_found -> empty in
          let t'' = ins (r, t') in
          Node (v, M.add x t'' m)
    in
    ins (l, t)

  let replace l v t =
    let rec ins = function
      | [], Node (_, m) -> Node (v, m)
      | x :: r, Node (v, m) ->
          let t' = try M.find x m with Not_found -> empty in
          let t'' = ins (r, t') in
          Node (v, M.add x t'' m)
    in
    ins (l, t)

  (*s When removing a binding, we take care of not leaving bindings to empty
      sub-tries in the nodes. Therefore, we test wether the result [t'] of
      the recursive call is the empty trie [empty]: if so, we just remove
      the branching with [M.remove]; otherwise, we modify it with [M.add]. *)

  let rec remove l t =
    match (l, t) with
    | [], Node (_, m) -> Node ([], m)
    | x :: r, Node (v, m) -> (
        try
          let t' = remove r (M.find x m) in
          Node (v, if t' = empty then M.remove x m else M.add x t' m)
        with Not_found -> t)

  (*s The iterators [map], [mapi], [iter] and [fold] are implemented in
      a straigthforward way using the corresponding iterators [M.map],
      [M.mapi], [M.iter] and [M.fold]. For the last three of them,
      we have to remember the path from the root, as an extra argument
      [revp]. Since elements are pushed in reverse order in [revp],
      we have to reverse it with [List.rev] when the actual binding
      has to be passed to function [f]. *)

  let rec map f = function
    | Node (v, m) -> Node (List.map f v, M.map (map f) m)

  let mapi f t =
    let rec maprec revp = function
      | Node (v, m) ->
          Node
            (List.map (f (List.rev revp)) v, M.mapi (fun x -> maprec (x :: revp)) m)
    in
    maprec [] t

  let iter f t =
    let rec traverse revp = function
      | Node (v, m) ->
          List.iter (f (List.rev revp)) v;
          M.iter (fun x t -> traverse (x :: revp) t) m
    in
    traverse [] t

  let fold f t acc =
    let rec traverse revp t acc =
      match t with
      | Node (v, m) ->
          List.fold_right (f (List.rev revp)) v (M.fold (fun x -> traverse (x :: revp)) m acc)
    in
    traverse [] t acc

  let compare cmp a b =
    let rec comp a b =
      match (a, b) with
      | Node (a, m1), Node (b, m2) ->
          let c = List.compare cmp a b in
          if c <> 0 then c else M.compare comp m1 m2
    in
    comp a b

  let equal eq a b =
    let rec comp a b =
      match (a, b) with
      | Node (a, m1), Node (b, m2) -> List.equal eq a b && M.equal comp m1 m2
    in
    comp a b

  (* The base case is rather stupid, but constructable *)
  let is_empty = function Node ([], m1) -> M.is_empty m1 | _ -> false

  let rec pp (ppelem : Format.formatter -> 'a -> unit) (fmt : Format.formatter)
      (Node (a, b) : 'a t) : unit =
    Format.fprintf fmt "[values:{";
    Elpi_util.Util.pplist ppelem "; " fmt a;
    Format.fprintf fmt "} key:{";
    M.pp (pp ppelem) fmt b;
    Format.fprintf fmt "}]"

  let show (fmt : Format.formatter -> 'a -> unit) (n : 'a t) : string =
    let b = Buffer.create 22 in
    Format.fprintf (Format.formatter_of_buffer b) "@[%a@]" (pp fmt) n;
    Buffer.contents b
end
