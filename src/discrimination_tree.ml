(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Elpi_util.Util

let arity_bits = 4
let k_bits = 2

(* 4 constructors encoded as: kno, arity, arg_value *)
let kConstant = 0
let kPrimitive = 1
let kVariable = 2
let kOther = 3
let k_lshift = Sys.int_size - k_bits
let ka_lshift = Sys.int_size - k_bits - arity_bits
let k_mask = ((1 lsl k_bits) - 1) lsl k_lshift
let arity_mask = (((1 lsl arity_bits) lsl k_bits) - 1) lsl ka_lshift
let data_mask = (1 lsl ka_lshift) - 1

(** [encode k c a]: 
   - k : the "constuctor" (kConstant, kPrimitive, kVariable, kOther)
   - c : the "data"
   - a : the "arity"
*)
let encode k c a = (k lsl k_lshift) lor (a lsl ka_lshift) lor (c land data_mask)

let k_of n = (n land k_mask) lsr k_lshift

let arity_of n =
  let k = k_of n in
  if k == kConstant then (n land arity_mask) lsr ka_lshift else 0

let mkConstant ~safe c a =
  let rc = encode kConstant c a in
  if safe && (abs c > data_mask || a >= 1 lsl arity_bits) then
    anomaly (Printf.sprintf "Indexing at depth > 1 is unsupported since constant %d/%d is too large or wide" c a);
  rc

let mkVariable = encode kVariable 0 0
let mkOther = encode kOther 0 0
let mkPrimitive c = encode kPrimitive (CData.hash c lsl k_bits) 0
let mkInputMode = encode kOther 1 0
let mkOutputMode = encode kOther 2 0
let mkMultivariable = encode kOther 3 0
let mkListHead = encode kOther 4 0
let mkListEnd = encode kOther 5 0
let () = assert (k_of (mkConstant ~safe:false ~-17 0) == kConstant)
let () = assert (k_of mkVariable == kVariable)
let () = assert (k_of mkOther == kOther)
let isVariable x = x == mkVariable
let isOther x = x == mkOther
let isInput x = x == mkInputMode
let isOutput x = x == mkOutputMode
let isMultivariable x = x == mkMultivariable
let isListHead x = x == mkListHead
let isListEnd x = x == mkListEnd

type cell = int

let pp_cell fmt n =
  let k = k_of n in
  if k == kConstant then
    let data = data_mask land n in
    let arity = (arity_mask land n) lsr ka_lshift in
    Format.fprintf fmt "Constant(%d,%d)" data arity
  else if k == kVariable then Format.fprintf fmt "Variable"
  else if k == kOther then
    Format.fprintf fmt
      (if isInput n then "Input"
       else if isOutput n then "Output"
       else if isMultivariable n then "Multivarible"
       else if isListHead n then "ListHead"
       else if isListEnd n then "ListEnd"
       else "Other")
  else if k == kPrimitive then Format.fprintf fmt "Primitive"
  else Format.fprintf fmt "%o" k

let show_cell n = Format.asprintf "%a" pp_cell n

module Trie = struct
  (*
   * Trie: maps over lists.
   * Note: This code is a heavily modified version of the original code.
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
  type 'a t = Node of { data : 'a list; other : 'a t option; multivariable : 'a t option; map : 'a t Ptmap.t }

  let empty = Node { data = []; other = None; multivariable = None; map = Ptmap.empty }

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
      | x :: r, Node ({ multivariable } as t) when isMultivariable x ->
          let t' = match multivariable with None -> empty | Some x -> x in
          let t'' = ins (r, t') in
          Node { t with multivariable = Some t'' }
      | x :: r, Node ({ map } as t) ->
          let t' = try Ptmap.find x map with Not_found -> empty in
          let t'' = ins (r, t') in
          Node { t with map = Ptmap.add x t'' map }
    in
    ins (l, t)

  let rec pp (ppelem : Format.formatter -> 'a -> unit) (fmt : Format.formatter)
      (Node { data; other; multivariable; map } : 'a t) : unit =
    Format.fprintf fmt "[values:{";
    pplist ppelem "; " fmt data;
    Format.fprintf fmt "} other:{";
    (match other with None -> () | Some m -> pp ppelem fmt m);
    Format.fprintf fmt "} multivariable:{";
    (match multivariable with None -> () | Some m -> pp ppelem fmt m);
    Format.fprintf fmt "} key:{";
    Ptmap.to_list map
    |> pplist
         (fun fmt (k, v) ->
           pp_cell fmt k;
           pp ppelem fmt v)
         "; " fmt;
    Format.fprintf fmt "}]"

  let show (fmt : Format.formatter -> 'a -> unit) (n : 'a t) : string =
    let b = Buffer.create 22 in
    Format.fprintf (Format.formatter_of_buffer b) "@[%a@]" (pp fmt) n;
    Buffer.contents b
end

type path = cell list [@@deriving show]

let compare x y = x - y

let skip hd tl : path =
  let rec aux arity path =
    if arity = 0 then path else match path with [] -> assert false | m :: tl -> aux (arity - 1 + arity_of m) tl
  in
  aux (arity_of hd) tl

(**
  Takes a path and skip a multivariable:
    we take the node just after the first occurrence of isListEnd or isMultivariable
    with no corresponding isListHead
*)
let skip_multivariable tl =
  let rec aux = function
    | hd :: tl, acc when isListHead hd -> aux (tl, acc + 1)
    | hd :: tl, 0 when isListEnd hd || isMultivariable hd -> tl
    | hd :: tl, acc when isListEnd hd -> aux (tl, acc - 1)
    | _ :: _, -1 | [], _ -> anomaly "Invalid negative guard"
    | _ :: tl, n -> aux (tl, n)
  in
  aux (tl, 0)

type 'a t = ('a * int) Trie.t

let pp pp_a fmt (t : 'a t) : unit = Trie.pp (fun fmt (a, _) -> pp_a fmt a) fmt t
let show pp_a (t : 'a t) : string = Trie.show (fun fmt (a, _) -> pp_a fmt a) t
let empty = Trie.empty
let index tree ps info ~time = Trie.add ps (info, time) tree

(* the equivalent of skip, but on the index, thus the list of trees
    that are rooted just after the term represented by the tree root
    are returned (we are skipping the root) *)
let all_children map other =
  let rec get_from_function n = function
    | Trie.Node { other = None; map } as tree ->
        if n = 0 then [ tree ] else Ptmap.fold (fun k v res -> get_from_function (n - 1 + arity_of k) v @ res) map []
    | Trie.Node { other = Some other; map } as tree ->
        if n = 0 then [ tree; other ]
        else Ptmap.fold (fun k v res -> get_from_function (n - 1 + arity_of k) v @ res) map [ other ]
  in
  let new_n n k = if isListHead k then n + 1 else if isListEnd k then n - 1 else n in
  let rec get_from_list n = function
    | Trie.Node { other = None; map } as tree ->
        if n = 0 then [ tree ] else Ptmap.fold (fun k v res -> get_from_list (new_n n k) v @ res) map []
    | Trie.Node { other = Some other; map } as tree ->
        if n = 0 then [ tree; other ] else Ptmap.fold (fun k v res -> get_from_list (new_n n k) v @ res) map [ other ]
  in
  let some_to_list = function Some x -> [ x ] | None -> [] in
  Ptmap.fold
    (fun k v res ->
      (* pp_string Format.std_formatter "\n\nThe current cell is: "; *)
      (* pp_cell Format.std_formatter k; *)
      (* pp_string Format.std_formatter "\n\n "; *)
      if isListHead k then get_from_list 1 v @ res else get_from_function (arity_of k) v @ res)
    map (some_to_list other)

let skip_multivar_trie (Trie.Node { other; map; multivariable }) : 'a Trie.t list =
  let new_n n k = if isListHead k then n + 1 else if isListEnd k then n - 1 else n in
  let rec get_from_list n = function
    | Trie.Node { other = None; map; multivariable } as tree ->
        if n = 0 then [ tree ]
        else
          Ptmap.fold
            (fun k v res ->
              (* pp_string Format.std_formatter "The key is:";
                 pp_cell Format.std_formatter k;
                 pp_string Format.std_formatter "\n\n"; *)
              get_from_list (new_n n k) v @ res)
            map
            (match multivariable with None -> [] | Some a -> [ a ])
    | Trie.Node { other = Some other; map; multivariable } as tree ->
        if n = 0 then [ tree; other ]
        else
          Ptmap.fold
            (fun k v res ->
              (* pp_string Format.std_formatter "The key is:";
                 pp_cell Format.std_formatter k;
                 pp_string Format.std_formatter "\n\n"; *)
              get_from_list (new_n n k) v @ res)
            map
            (other :: (match multivariable with None -> [] | Some a -> [ a ]))
  in
  let some_to_list = function Some x -> [ x ] | None -> [] in
  (match other with None -> [] | Some a -> get_from_list 1 a)
  @ Ptmap.fold
      (fun k v res ->
        (* pp_string Format.std_formatter "The current key is";
           pp_cell Format.std_formatter k;
           pp_string Format.std_formatter "\n"; *)
        if isListEnd k then v :: res else get_from_list 1 v @ res)
      map (some_to_list multivariable)

(* NOTE: l1 and l2 are supposed to be sorted *)
let rec merge (l1 : ('a * int) list) l2 =
  match (l1, l2) with
  | [], l | l, [] -> l
  | ((_, tx) as x) :: xs, (_, ty) :: _ when tx > ty -> x :: merge xs l2
  | _, y :: ys -> y :: merge l1 ys

let get_all_children v mode = isOther v || (isVariable v && isOutput mode)

(* get_all_children returns if a key should be unified with all the values of
   the current sub-tree. This key should be either K.to_unfy or K.variable.
   In the latter case, the mode boolean to be true (we are in output mode). *)
let rec retrieve_aux (mode : cell) path = function
  | [] -> []
  | hd :: tl -> merge (retrieve mode path hd) (retrieve_aux mode path tl)

and retrieve mode path (tree : ('a * cell) Trie.t) =
  match (tree, path) with
  | Trie.Node { data }, [] -> data
  | node, hd :: tl when isInput hd || isOutput hd -> retrieve hd tl tree
  | node, hd :: tl when isMultivariable hd || isListEnd hd ->
      (* assert false; *)
      (* pp_string Format.std_formatter "In multivariable branch\n"; *)
      (* pp (fun fmt _ -> pp_string fmt "+") Format.std_formatter node; *)
      (* pp_string Format.std_formatter "\n\n"; *)
      let sub_tries = skip_multivar_trie node in
      (* pp_string Format.std_formatter "Sub-tries list is\n"; *)
      (* pplist (pp (fun fmt _ -> pp_string fmt "+")) ";" Format.std_formatter sub_tries; *)
      (* pp_string Format.std_formatter "\n\n"; *)
      retrieve_aux mode tl sub_tries
  | Trie.Node { map; other; multivariable }, hd :: tl when get_all_children hd mode -> (
      (* TODO: Be carefull: if the head of the trie is a ListHead then we should get the children after the corresponding ListEnd  *)
      (* pp_string Format.std_formatter "\n\nIn get_all_children branch\n"; *)
      (* pp (fun fmt _ -> pp_string fmt "+") Format.std_formatter tree; *)
      (* pp_string Format.std_formatter "\nThe all_children are\n"; *)
      (* pplist (pp (fun fmt _ -> pp_string fmt "+")) ";" Format.std_formatter (all_children map other); *)
      (* assert false; *)
      let from_map = retrieve_aux mode tl (all_children map other) in
      (* pp_string Format.std_formatter "\n the result is\n"; *)
      (* pp (fun fmt _ -> pp_string fmt "+") Format.std_formatter tree; *)
      (* pplist (fun fmt _ -> pp_string fmt "+") ";" Format.std_formatter from_map; *)
      (* pp_string Format.std_formatter "\n\n"; *)
      match multivariable with
      | None -> from_map
      | Some a ->
          (* pp_string Format.std_formatter " Before error?\n"; *)
          (* pp_path Format.std_formatter path; *)
          let skipped_path = skip_multivariable tl in
          (* pp_string Format.std_formatter "\nSkipped path is\n"; *)
          (* pp_path Format.std_formatter skipped_path; *)
          (* pp_string Format.std_formatter "\n\n"; *)
          let retrive_multivariable = retrieve mode skipped_path a in
          (* pp_string Format.std_formatter "Tretrieved multivariable is\n"; *)
          (* pplist ( (fun fmt _ -> pp_string fmt "+")) ";" Format.std_formatter retrive_multivariable; *)
          (* pp_string Format.std_formatter "\n\n"; *)
          merge from_map retrive_multivariable)
  | Trie.Node { other; map; multivariable }, hd :: tl -> (
      (* pp_string Format.std_formatter "\nIn last branch\n"; *)
      (* pp_path Format.std_formatter path; *)
      (* pp_string Format.std_formatter "\nThe subtrie is\n"; *)
      (* pp (fun fmt _ -> pp_string fmt "+") Format.std_formatter tree; *)
      let xxx =
        if isInput mode && isVariable hd then []
        else
          let subtree = try Ptmap.find hd map with Not_found -> Trie.empty in
          (* pp_string Format.std_formatter "\n1\n"; *)
          (* pp_string Format.std_formatter "\nThe subssubtrie is\n"; *)
          (* pp (fun fmt _ -> pp_string fmt "+") Format.std_formatter subtree; *)
          retrieve mode tl subtree
      in
      (* pp_string Format.std_formatter "\nBefore \n"; *)
      (* pp_path Format.std_formatter tl; *)
      (* pp_string Format.std_formatter "\n After\n"; *)
      match (other, multivariable) with
      | None, None -> xxx
      | Some a, None -> merge xxx (retrieve mode (skip hd tl) a)
      | None, Some a ->
          (* pp_string Format.std_formatter "\nIn multivariable sub sub section\n"; *)
          merge xxx (retrieve mode (skip_multivariable tl) a)
      | Some a, Some b -> merge (merge xxx (retrieve mode (skip hd tl) a)) (retrieve mode (skip_multivariable tl) b))

let retrieve path index =
  match path with
  | [] -> anomaly "A path should at least of length 2"
  | mode :: tl -> retrieve mode tl index |> List.map fst
