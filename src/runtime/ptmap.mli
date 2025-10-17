(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(** Maps over integers implemented as Patricia trees.

   The following signature is a subset of [Map.S with type key = int],
   with the same specifications (not repeated here) unless specified
   otherwise.

   These are little-endian Patricia trees, so there is no efficient
   ordering of keys within the structure. Consequently,
   - [min/max_binding], [find_first/last] are rather inefficient (linear)
   - [iter], [fold] *do not* iterate in the key order
   - [bindings] is *not sorted* by keys
*)

type key = int

type (+'a) t

val empty: 'a t

val is_empty: 'a t -> bool

val mem: key -> 'a t -> bool

val add: key -> 'a -> 'a t -> 'a t

val update: key -> ('a option -> 'a option) -> 'a t -> 'a t

val singleton: key -> 'a -> 'a t

val remove: key -> 'a t -> 'a t

val merge:
         (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t

val union: (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int

val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

val iter: (key -> 'a -> unit) -> 'a t -> unit

val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

val for_all: (key -> 'a -> bool) -> 'a t -> bool

val exists: (key -> 'a -> bool) -> 'a t -> bool

val filter: (key -> 'a -> bool) -> 'a t -> 'a t

val filter_map: (key -> 'a -> 'b option) -> 'a t -> 'b t

val partition: (key -> 'a -> bool) -> 'a t -> 'a t * 'a t

val cardinal: 'a t -> int

val bindings: 'a t -> (key * 'a) list

val min_binding: 'a t -> (key * 'a)

val min_binding_opt: 'a t -> (key * 'a) option

val max_binding: 'a t -> (key * 'a)

val max_binding_opt: 'a t -> (key * 'a) option

val choose: 'a t -> (key * 'a)

val choose_opt: 'a t -> (key * 'a) option

val split: key -> 'a t -> 'a t * 'a option * 'a t

val find: key -> 'a t -> 'a

val find_opt: key -> 'a t -> 'a option

val find_first: (key -> bool) -> 'a t -> key * 'a

val find_first_opt: (key -> bool) -> 'a t -> (key * 'a) option

val find_last: (key -> bool) -> 'a t -> key * 'a

val find_last_opt: (key -> bool) -> 'a t -> (key * 'a) option

val map: ('a -> 'b) -> 'a t -> 'b t

val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t

val to_seq : 'a t -> (key * 'a) Seq.t

val to_seq_from : key -> 'a t -> (key * 'a) Seq.t

val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t

val of_seq : (key * 'a) Seq.t -> 'a t

(********************************************************)

(* Specific to a scenario where the key is computed starting from a term
     functor(args)
   If the key of items in the map was computed such that
   flexible args are made of 1 (read provides)
   and the query is computed such that
   flexible args are made of 0 (read requires)
   then find_unifiables returns all elements with a key
   such that
     query_args land key_args == query_args
   i.e. all items that could unify with the query.
   The result is in no precise order. *)
val find_unifiables : int -> 'a t -> 'a list

val to_list : 'a t -> (int * 'a) list
val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
val show : (Format.formatter -> 'a -> unit) -> 'a t -> string
