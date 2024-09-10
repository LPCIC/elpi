type 'a t
val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
val show : (Format.formatter -> 'a -> unit) -> 'a t -> string

type  'a l = Nil | Cons of { head : 'a; last : unit; tail : 'a l }
[@@deriving show, ord]

val empty : unit -> 'a t
val cons : 'a -> 'a t -> 'a t
val rcons : 'a -> 'a t -> 'a t
val replace : ('a -> bool) -> 'a -> 'a t -> unit
val insert_before : ('a -> bool) -> 'a -> 'a t -> 'a t
val insert_after : ('a -> bool) -> 'a -> 'a t -> unit
val commit : 'a t -> 'a l
val commit_map : ('a -> 'b) -> 'a t -> 'b l
val to_list : 'a l -> 'a list
