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

(*s Maps over integers implemented as Patricia trees.
    The following signature is exactly [Map.S with type key = int],
    with the same specifications. *)

type (+'a) t

type key = int

val empty : 'a t

val is_empty : 'a t -> bool

val add : int -> 'a -> 'a t -> 'a t

val find : int -> 'a t -> 'a

val remove : int -> 'a t -> 'a t

val mem :  int -> 'a t -> bool

val iter : (int -> 'a -> unit) -> 'a t -> unit

val map : ('a -> 'b) -> 'a t -> 'b t

val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t

val fold : (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

(* Specific to a scenario where the key is computed starting from a term
     functor(args)
   and reserves the lower functor_bits for the functor.

   If the key of items in the map was computed such that
     key = | bits for the args | bits for the functor |
   where flexible args are made of 1 (read provides)
   and the query is computed such that
     query = | bits for the args | bits for the functor |
   where flexible args are made of 0 (read requires)
   and the bits for the main functor are functor_bits many,
   then find_unifiables returns all elements with a key
   that matches verbatim the functor part and such that
     query_args land key_args == query_args
   i.e. all items that could unify with the query.
   The result is in no precise order. *)
val find_unifiables : functor_bits:int -> int -> 'a t -> 'a list

(* diff f m1 m2 is the map whose domain is (Dom(m1) \ Dom(m2)) \cup m3
   where m3 = { x | x \in m1 \cap m2 && f (m1 x) (m2 x) != None } and
   (diff f m1 m2)(x) = y when x \in m3 and f (m1 x) (m2 x) = Some y
   (diff f m1 m2)(x) = m1(x) when x \in Dom(m1) \ Dom(m2) *)
val diff : ('a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t

val to_list : 'a t -> (int * 'a) list
