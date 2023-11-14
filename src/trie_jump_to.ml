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


module Make (M : Map.S) = struct
  
(*s Then a trie_jump_to is a variant of a trie for term representation
    where a node contains a point to its desendents and its successor *)

  type key = M.key list

  type 'a t = Node of 'a option * 'a t M.t * 'a t M.t list

  let empty = Node (None, M.empty, [])

(*s To find a mapping in a trie is easy: when all the elements of the
    key have been read, we just inspect the optional info at the
    current node; otherwise, we descend in the appropriate sub-trie
    using [M.find]. *)

  let rec find l t = match (l,t) with
    | [], Node (None,_,_)   -> raise Not_found
    | [], Node (Some v,_,_) -> v
    | x::r, Node (_,m,_)    -> find r (M.find x m)

  let mem l t = 
    try Fun.const true (find l t) with Not_found -> false

(*s Insertion is more subtle. When the final node is reached, we just
    put the information ([Some v]). Otherwise, we have to insert the
    binding in the appropriate sub-trie [t']. But it may not exists,
    and in that case [t'] is bound to an empty trie. Then we get a new
    sub-trie [t''] by a recursive insertion and we modify the
    branching, so that it now points to [t''], with [M.add]. *)

  let add l v t =
    let rec ins = function
      | [], Node (_,m,succ) -> Node (Some v,m,failwith "" :: succ)
      | x::r, Node (v,m,succ) ->
        let t' = try M.find x m with Not_found -> empty in
        let t'' = ins (r,t') in
        Node (v, M.add x t'' m, failwith "" :: succ)
    in
    ins (l,t)

(*s When removing a binding, we take care of not leaving bindings to empty
    sub-tries in the nodes. Therefore, we test wether the result [t'] of 
    the recursive call is the empty trie [empty]: if so, we just remove
    the branching with [M.remove]; otherwise, we modify it with [M.add]. *)

  let remove l t = match (l,t) with
    | [], Node (_,m,_) -> failwith "Here we should remove the succ from all of those pointing to m"
    | x::r, Node (v,m, _) -> failwith "Same as before"

(*s The iterators [map], [mapi], [iter] and [fold] are implemented in
    a straigthforward way using the corresponding iterators [M.map],
    [M.mapi], [M.iter] and [M.fold]. For the last three of them,
    we have to remember the path from the root, as an extra argument
    [revp]. Since elements are pushed in reverse order in [revp],
    we have to reverse it with [List.rev] when the actual binding 
    has to be passed to function [f]. *)

  let rec map f = function
    | Node (None,m,s)   -> Node (None, M.map (map f) m,s)
    | Node (Some v,m,s) -> Node (Some (f v), M.map (map f) m,s)

  let mapi f t =
    let rec maprec revp = function
      | Node (None,m,s) -> Node (None, M.mapi (fun x -> maprec (x::revp)) m,s)
      | Node (Some v,m,s) -> 
          Node (Some (f (List.rev revp) v), M.mapi (fun x -> maprec (x::revp)) m,s)
    in
    maprec [] t

  let iter f t =
    let rec traverse revp = function
      | Node (None,m,s) -> M.iter (fun x -> traverse (x::revp)) m
      | Node (Some v,m,s) ->
	        f (List.rev revp) v; 
          M.iter (fun x t -> traverse (x::revp) t) m
    in
    traverse [] t

  let fold f t acc =
    let rec traverse revp t acc = match t with
      | Node (None,m,s) -> M.fold (fun x -> traverse (x::revp)) m acc
      | Node (Some v,m,s) -> 
	      f (List.rev revp) v (M.fold (fun x -> traverse (x::revp)) m acc)
    in
    traverse [] t acc

  let compare cmp a b =
    let rec comp a b = match a,b with
      | Node (Some _, _, _), Node (None, _, _) -> 1
      | Node (None, _, _), Node (Some _, _, _) -> -1
      | Node (None, m1,s1), Node (None, m2, s2) -> M.compare comp m1 m2
      (* TODO: compare also s1 and s2 *)
      | Node (Some a, m1, s1), Node (Some b, m2, s2) ->
        let c = cmp a b in
      (* TODO: compare also s1 and s2 *)
        if c <> 0 then c else M.compare comp m1 m2
    in
    comp a b

  let equal eq a b =
    let rec comp a b = match a,b with
      | Node (None, m1, s1), Node (None, m2, s2) -> M.equal comp m1 m2
      (* TODO: compare also s1 and s2 *)
      | Node (Some a, m1, s1), Node (Some b, m2, s2) -> eq a b && M.equal comp m1 m2
      (* TODO: compare also s1 and s2 *)
      | _ -> false
    in
    comp a b

  (* The base case is rather stupid, but constructable *)
  let is_empty = function
    | Node (None, m1, _) -> M.is_empty m1
    | _ -> false
    
  let rec pp (f: (Format.formatter -> 'a -> unit)) (fmt: Format.formatter) (m: 'a t) =
    let print_key k = Printf.printf "k: " in
    (match m with 
      | Node (None, sons,_) -> Printf.printf "None ["; M.iter (fun k v -> print_key k; Printf.printf " v:"; pp f fmt v) sons; Printf.printf "]"
      | Node (Some k, sons,_) -> Printf.printf "Some ["; print_key k; M.iter (fun k v -> pp f fmt v) sons); Printf.printf "]"

  (*  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t  *)
  let show f m =
    let b = Buffer.create 20 in
    let fmt = Format.formatter_of_buffer b in
    pp f fmt m;
    Buffer.contents b
end
