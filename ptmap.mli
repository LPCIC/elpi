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
