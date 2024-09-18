(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

(* functional lists with O(1) rcons *)

type 'a t
val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
val show : (Format.formatter -> 'a -> unit) -> 'a t -> string

val empty : unit -> 'a t
val cons : 'a -> 'a t -> 'a t
val rcons : 'a -> 'a t -> 'a t

val replace : ('a -> bool) -> 'a -> 'a t -> 'a t
val remove : ('a -> bool) -> 'a t -> 'a t

(* [insert f x l] inserts before y in l if f y > 0 *)
val insert : ('a -> int) -> 'a -> 'a t -> 'a t
val remove : ('a -> bool) -> 'a t -> 'a t

type 'a scan
val to_scan : 'a t -> 'a scan
val is_empty : 'a scan -> bool
val next : 'a scan -> 'a * 'a scan
val to_list : 'a scan -> 'a list
val of_list : 'a list -> 'a scan
val length : 'a scan -> int

