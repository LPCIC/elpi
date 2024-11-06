(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)
open Elpi_util.Util


(* each path element is one of these 4 "constructors" *)
let kConstant = 0  (* p, q *)
let kPrimitive = 1 (* 3, "foo" *)
let kVariable = 2  (* X1, _ *)
let kOther = 3     (* Lam + internal tags for list-begin/end, input, output, list-tail-variable *)

(* 4 constructors encoded as: kno, arity, arg_value *)
let arity_bits = 4
let k_bits = 2

(** [encode k c a]: 
   - k : the "constuctor" (kConstant, kPrimitive, kVariable, kOther)
   - c : the "data"
   - a : the "arity"
*)
let cell_size = Sys.int_size
let k_lshift = cell_size - k_bits
let ka_lshift = cell_size - k_bits - arity_bits
let k_mask = ((1 lsl k_bits) - 1) lsl k_lshift
let arity_mask = (((1 lsl arity_bits) lsl k_bits) - 1) lsl ka_lshift
let data_mask = (1 lsl ka_lshift) - 1
let encode ~k ~arity ~data  = (k lsl k_lshift) lor (arity lsl ka_lshift) lor (data land data_mask)

let k_of n = (n land k_mask) lsr k_lshift

let arity_of n =
  let k = k_of n in
  if k == kConstant then (n land arity_mask) lsr ka_lshift else 0

let data_of n =
  (n land data_mask)

let mkConstant ~safe ~data ~arity =
  let rc = encode ~k:kConstant ~data ~arity in
  if safe && (abs data > data_mask || arity >= 1 lsl arity_bits) then
    anomaly (Printf.sprintf "Indexing at depth > 1 is unsupported since constant %d/%d is too large or wide" data arity);
  rc

let mkPrimitive c = encode ~k:kPrimitive ~data:(CData.hash c lsl k_bits) ~arity:0

let mkVariable = encode ~k:kVariable ~data:0 ~arity:0
let mkLam = encode ~k:kOther ~data:0 ~arity:0

(* each argument starts with its mode *)
let mkInputMode = encode ~k:kOther ~data:1 ~arity:0
let mkOutputMode = encode ~k:kOther ~data:2 ~arity:0
let mkListTailVariable = encode ~k:kOther ~data:3 ~arity:0
let mkListHead = encode ~k:kOther ~data:4 ~arity:0
let mkListEnd = encode ~k:kOther ~data:5 ~arity:0 
let mkPathEnd = encode ~k:kOther ~data:6 ~arity:0


let isVariable x = x == mkVariable
let isLam x = x == mkLam
let isInput x = x == mkInputMode
let isOutput x = x == mkOutputMode
let isListHead x = x == mkListHead
let isListEnd x = x == mkListEnd
let isListTailVariable x = x == mkListTailVariable
let isPathEnd x = x == mkPathEnd

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
       else if isListTailVariable n then "ListTailVariable"
       else if isListHead n then "ListHead"
       else if isListEnd n then "ListEnd"
       else if isPathEnd n then "PathEnd"
       else "Other")
  else if k == kPrimitive then Format.fprintf fmt "Primitive"
  else Format.fprintf fmt "%o" k

let show_cell n = Format.asprintf "%a" pp_cell n
module Path : sig
  type t
  val pp : Format.formatter -> t -> unit
  val get : t -> int -> cell
  type builder
  val make : int -> cell -> builder
  val emit : builder -> cell -> unit
  val stop : builder -> t
  val of_list : cell list -> t

end = struct
 type t = cell array [@@deriving show]
 let get a i = a.(i)

 type builder = { mutable pos : int; mutable path : cell array }
 let make size e = { pos = 0; path = Array.make size e }
 let rec emit p e = 
    let len = Array.length p.path in
    if p.pos < len - 1 then begin
      Array.unsafe_set p.path p.pos e;
      p.pos <- p.pos + 1
    end else begin
      let newpath = Array.make (2 * len) mkPathEnd in
      Array.blit p.path 0 newpath 0 len;
      p.path <- newpath;
      emit p e
    end
 let stop { path } = path

 let of_list l =
  let path = make 1 (List.hd l) in
  List.iter (emit path) l;
  stop path
  
end

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

  type 'a t = Node of {
    data : 'a list;
    (* children *)
    other : 'a t option;             (* for Other, Variable *)
    listTailVariable : 'a t option;  (* for ListTailVariable *)
    map : 'a t Ptmap.t;              (* for Constant, Primitive, ListHead, ListEnd *)
  }

  let empty = Node { data = []; other = None; listTailVariable = None; map = Ptmap.empty }

  let is_empty x = x == empty

  let rec replace p x = function
    | Node { data; other; listTailVariable; map } ->
        Node {
          data = data |> List.map (fun y -> if p y then x else y);
          other = other |> Option.map (replace p x);
          listTailVariable = listTailVariable |> Option.map (replace p x);
          map = map |> Ptmap.map (replace p x);
        }
      
  let rec remove f = function
    | Node { data; other; listTailVariable; map } ->
        Node {
          data = data |> List.filter (fun x -> not (f x));
          other = other |> Option.map (remove f);
          listTailVariable = listTailVariable |> Option.map (remove f);
          map = map |> Ptmap.map (remove f);
        }

  let add (a : Path.t) v t =
    let max = ref 0 in
    let rec ins ~pos = let x = Path.get a pos in function
      | Node ({ data } as t) when isPathEnd x -> max := pos; Node { t with data = v :: data }
      | Node ({ other } as t) when isVariable x || isLam x ->
          let t' = match other with None -> empty | Some x -> x in
          let t'' = ins ~pos:(pos+1) t' in
          Node { t with other = Some t'' }
      | Node ({ listTailVariable } as t) when isListTailVariable x ->
          let t' = match listTailVariable with None -> empty | Some x -> x in
          let t'' = ins ~pos:(pos+1) t' in
          Node { t with listTailVariable = Some t'' }
      | Node ({ map } as t) ->
          let t' = try Ptmap.find x map with Not_found -> empty in
          let t'' = ins ~pos:(pos+1) t' in
          Node { t with map = Ptmap.add x t'' map }
    in
    let t = ins ~pos:0 t in
    t, !max

  let rec pp (ppelem : Format.formatter -> 'a -> unit) (fmt : Format.formatter)
      (Node { data; other; listTailVariable; map } : 'a t) : unit =
    Format.fprintf fmt "@[<v>[values:{";
    pplist ppelem "; " fmt data;
    Format.fprintf fmt "}@ other:{";
    (match other with None -> () | Some m -> pp ppelem fmt m);
    Format.fprintf fmt "}@ listTailVariable:{";
    (match listTailVariable with None -> () | Some m -> pp ppelem fmt m);
    Format.fprintf fmt "}@ key:{@[<hov 2>";
    Ptmap.to_list map
    |> pplist
         (fun fmt (k, v) ->
           pp_cell fmt k;
           pp ppelem fmt v)
         ";@ " fmt;
    Format.fprintf fmt "@]}]@]"

  let show (fmt : Format.formatter -> 'a -> unit) (n : 'a t) : string =
    let b = Buffer.create 22 in
    Format.fprintf (Format.formatter_of_buffer b) "@[%a@]" (pp fmt) n;
    Buffer.contents b
end


let update_par_count n k =
  if isListHead k then n + 1 else
  if isListEnd k || isListTailVariable k then n - 1 else n

let skip ~pos path (*hd tl*) : int =
  let rec aux_list acc p =
    if acc = 0 then p
    else aux_list (update_par_count acc (Path.get path p)) (p+1)
  in
  let rec aux_const arity p =
    if arity = 0 then p
    else
      if isListHead (Path.get path p) then
        let skip_list = aux_list 1 (p+1) in
        aux_const (arity - 1) skip_list
      else aux_const (arity - 1 + arity_of (Path.get path p)) (p+1)
  in
  if isListHead (Path.get path pos) then aux_list 1 (pos+1) else aux_const (arity_of (Path.get path pos)) (pos+1)

(**
  Takes a path and skip a listTailVariable:
    we take the node just after the first occurrence of isListEnd or isListTailVariable
    with no corresponding isListHead
*)
let skip_listTailVariable ~pos path : int =
  let rec aux i pc =
    if pc = 0 then i
    else aux (i+1) (update_par_count pc (Path.get path i)) in
  aux (pos + 1) (update_par_count 1 (Path.get path pos))

(* A discrimination tree is a record {t; max_size; max_depths } where
   - t is a Trie for instance retrival 
   - max_size is a int representing the max size of a path in the Trie
   - max_depths is a int list representing the max depth of the each indexed arguments

  Note : 
  - max_size is used as an heuristic for the size of path when a new one is created
    (we use arrays, therefore we have to allocate them)
  - During the construction of a goal's path using max_depths, the goal's argument can
    be larger than that of the corresponding instances. If the indexing depth
    for an argument i is set to X by the user but the maximal depth of i in the
    database is Y (where Y is much less than X it is inefficient to build a path
    of height X for the goal. Instead, constructing a path of height Y is more
    efficient and can lead to performance gains. As an example, consider the following:
    ```elpi
      kind term type.
      type app list term -> term.
      type con string -> term.
      :index (100)
      pred p i:term.
      p (app[con "f", app[X]]).

      main :-
        p (app [con "f", app[app[app[...app[con "g"]]]]])
    ```
    In the example it is no needed to index the goal path to depth 100, but rather considering
    the maximal depth of the first argument, which 4 << 100
  *)
type 'a t = {t: 'a Trie.t; max_size : int;  max_depths : int array } 

let pp pp_a fmt { t } : unit = Trie.pp (fun fmt data -> pp_a fmt data) fmt t
let show pp_a { t } : string = Trie.show (fun fmt data -> pp_a fmt data) t

let index { t; max_size; max_depths } path data =
  let t, m = Trie.add path data t in
  { t; max_size = max max_size m; max_depths }

let max_path { max_size } = max_size
let max_depths { max_depths } = max_depths 

(* the equivalent of skip, but on the index, thus the list of trees
    that are rooted just after the term represented by the tree root
    are returned (we are skipping the root) *)
let call f =
  let res = ref @@ [] in
  let add_result x = res := x :: !res in
  f ~add_result; !res
  
let skip_to_listEnd ~add_result mode (Trie.Node { other; map; listTailVariable }) =
  let rec get_from_list n = function
    | Trie.Node { other = None; map; listTailVariable } as tree ->
        if n = 0 then add_result tree
        else
          (Ptmap.iter
            (fun k v -> get_from_list (update_par_count n k) v)
            map;
            match listTailVariable with None -> () | Some a -> add_result a)
    | Trie.Node { other = Some other; map; listTailVariable } as tree ->
        if n = 0 then (add_result tree; add_result other)
        else
          (get_from_list n other;
          Ptmap.iter
              (fun k v -> get_from_list (update_par_count n k) v)
              map;
            match listTailVariable with None -> () | Some a -> add_result a)
  in
  let some_to_list = function Some x -> add_result x | None -> () in
  (match other with None -> () | Some a -> get_from_list 1 a);
  if isOutput mode then Ptmap.iter (fun k v -> get_from_list (update_par_count 1 k) v) map;
  some_to_list listTailVariable

let skip_to_listEnd mode t = call (skip_to_listEnd mode t)

let get_all_children v mode = isLam v || (isVariable v && isOutput mode)

let rec retrieve ~pos ~add_result mode path tree : unit =
  let hd = Path.get path pos in
  let Trie.Node {data; map; other; listTailVariable} = tree in
  (* Format.eprintf "%d %a\n%!" pos pp_cell hd; *)
  if Trie.is_empty tree then ()
  else if isPathEnd hd then List.iter add_result data
  else if isInput hd || isOutput hd then 
    (* next argument, we update the mode *)
     retrieve ~pos:(pos+1) ~add_result hd path tree
  else if isListTailVariable hd then
    let sub_tries = skip_to_listEnd mode tree in
    List.iter (retrieve ~pos:(pos+1) ~add_result mode path) sub_tries
  else begin
    (* Here the constructor can be Constant, Primitive, Variable, Other, ListHead, ListEnd *)
    begin
      if get_all_children hd mode then 
        (* we take all the children in the map *)
        on_all_children ~pos:(pos+1) ~add_result mode path map
      else if isInput mode && isVariable hd then () (* no search has to be done in the map *)
      else
          (* we have a Constant, Primitive, ListHead or ListHead and look for the key in the map *)
          try retrieve ~pos:(pos+1) ~add_result mode path (Ptmap.find hd map)
          with Not_found -> ()
    end;
    (* moreover, we have to take into account other and listTailVariable since they represent UVar in the tree,
       therefore they can be unified with the hd *)
    if not(isListEnd hd) then Option.iter (fun a -> retrieve ~pos:(skip ~pos path) ~add_result mode path a) other;
    Option.iter (fun a -> retrieve ~pos:(skip_listTailVariable ~pos path) ~add_result mode path a) listTailVariable
  end

and on_all_children ~pos ~add_result mode path map =
  let rec skip_list par_count arity = function
    | Trie.Node { other; map; listTailVariable } as tree ->
        if par_count = 0 then begin
          skip_functor arity tree
        end else begin
          Ptmap.iter (fun k v -> skip_list (update_par_count par_count k) arity v) map;
          Option.iter (skip_list par_count arity) other;
          Option.iter (skip_list (par_count - 1) arity) listTailVariable
        end
  and skip_functor arity = function
    | Trie.Node { other; map } as tree ->
        Option.iter (retrieve ~pos ~add_result mode path) other;
        if arity = 0 then retrieve ~pos ~add_result mode path tree
        else
          Ptmap.iter (fun k v ->
              if isListHead k then skip_list 1 (arity - 1) v
              else skip_functor (arity - 1 + arity_of k) v)
            map
  in
  Ptmap.iter (fun k v ->
    if isListHead k then skip_list 1 0 v
    else skip_functor (arity_of k) v)
  map

let empty_dt args_depth : 'a t =
  let max_depths = Array.make (List.length args_depth) 0 in
  {t = Trie.empty; max_depths; max_size = 0}

let retrieve ~pos ~add_result path index =
  let mode = Path.get path pos in
  assert(isInput mode || isOutput mode);
  retrieve ~add_result mode ~pos:(pos+1) path index
  
let retrieve cmp_data path { t } = 
  let r = call (retrieve ~pos:0 path t) in
  Bl.of_list @@ List.sort cmp_data r

let replace p x i = { i with t = Trie.replace p x i.t }
let remove keep dt = { dt with t = Trie.remove keep dt.t}

module Internal = struct
  let kConstant = kConstant
  let kPrimitive = kPrimitive
  let kVariable = kVariable
  let kOther = kOther

  let k_of = k_of
  let arity_of = arity_of
  let data_of = data_of

  let isVariable = isVariable
  let isLam = isLam
  let isInput = isInput
  let isOutput = isOutput
  let isListHead = isListHead
  let isListEnd = isListEnd
  let isListTailVariable = isListTailVariable
  let isPathEnd = isPathEnd

end