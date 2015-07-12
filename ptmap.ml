(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*i $Id$ i*)

(*s Maps of integers implemented as Patricia trees, following Chris
    Okasaki and Andrew Gill's paper {\em Fast Mergeable Integer Maps}
    ({\tt\small http://www.cs.columbia.edu/\~{}cdo/papers.html\#ml98maps}).
    See the documentation of module [Ptset] which is also based on the
    same data-structure. *)

type key = int

type 'a t =
  | Empty
  | Leaf of int * 'a
  | Branch of int * int * 'a t * 'a t

let empty = Empty

let is_empty t = t = Empty

let zero_bit k m = (k land m) == 0

let rec mem k = function
  | Empty -> false
  | Leaf (j,_) -> k == j
  | Branch (_, m, l, r) -> mem k (if zero_bit k m then l else r)

let rec find k = function
  | Empty -> raise Not_found
  | Leaf (j,x) -> if k == j then x else raise Not_found
  | Branch (_, m, l, r) -> find k (if zero_bit k m then l else r)

let lowest_bit x = x land (-x)

let branching_bit p0 p1 = lowest_bit (p0 lxor p1)

let mask p m = p land (m-1)

let join (p0,t0,p1,t1) =
  let m = branching_bit p0 p1 in
  if zero_bit p0 m then 
    Branch (mask p0 m, m, t0, t1)
  else 
    Branch (mask p0 m, m, t1, t0)

let match_prefix k p m = (mask k m) == p

let add k x t =
  let rec ins = function
    | Empty -> Leaf (k,x)
    | Leaf (j,_) as t -> 
	if j == k then Leaf (k,x) else join (k, Leaf (k,x), j, t)
    | Branch (p,m,t0,t1) as t ->
	if match_prefix k p m then
	  if zero_bit k m then 
	    Branch (p, m, ins t0, t1)
	  else
	    Branch (p, m, t0, ins t1)
	else
	  join (k, Leaf (k,x), p, t)
  in
  ins t

let branch = function
  | (_,_,Empty,t) -> t
  | (_,_,t,Empty) -> t
  | (p,m,t0,t1)   -> Branch (p,m,t0,t1)

let remove k t =
  let rec rmv = function
    | Empty -> Empty
    | Leaf (j,_) as t -> if k == j then Empty else t
    | Branch (p,m,t0,t1) as t -> 
	if match_prefix k p m then
	  if zero_bit k m then
	    branch (p, m, rmv t0, t1)
	  else
	    branch (p, m, t0, rmv t1)
	else
	  t
  in
  rmv t

let rec iter f = function
  | Empty -> ()
  | Leaf (k,x) -> f k x
  | Branch (_,_,t0,t1) -> iter f t0; iter f t1

let rec map f = function
  | Empty -> Empty
  | Leaf (k,x) -> Leaf (k, f x)
  | Branch (p,m,t0,t1) -> Branch (p, m, map f t0, map f t1)
      
let rec mapi f = function
  | Empty -> Empty
  | Leaf (k,x) -> Leaf (k, f k x)
  | Branch (p,m,t0,t1) -> Branch (p, m, mapi f t0, mapi f t1)
      
let rec fold f s accu = match s with
  | Empty -> accu
  | Leaf (k,x) -> f k x accu
  | Branch (_,_,t0,t1) -> fold f t0 (fold f t1 accu)

(* we order constructors as Empty < Leaf < Branch *)
let compare cmp t1 t2 =
  let rec compare_aux t1 t2 = match t1,t2 with
    | Empty, Empty -> 0
    | Empty, _ -> -1
    | _, Empty -> 1
    | Leaf (k1,x1), Leaf (k2,x2) ->
	let c = compare k1 k2 in 
	if c <> 0 then c else cmp x1 x2
    | Leaf _, Branch _ -> -1
    | Branch _, Leaf _ -> 1
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
	let c = compare p1 p2 in
	if c <> 0 then c else
	let c = compare m1 m2 in
	if c <> 0 then c else
        let c = compare_aux l1 l2 in
        if c <> 0 then c else
        compare_aux r1 r2
  in
  compare_aux t1 t2

let equal eq t1 t2 =
  let rec equal_aux t1 t2 = match t1, t2 with
    | Empty, Empty -> true
    | Leaf (k1,x1), Leaf (k2,x2) -> k1 = k2 && eq x1 x2
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
	p1 = p2 && m1 = m2 && equal_aux l1 l2 && equal_aux r1 r2
    | _ -> false
  in
  equal_aux t1 t2
