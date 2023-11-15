module Make :
  functor (M : Elpi_util.Util.Map.S) ->
    sig
      type key = M.key list
      type 'a t = Node of 'a option * 'a t M.t
      val empty : 'a t
      val find : key -> 'a t -> 'a
      val mem : key -> 'a t -> bool
      val add : key -> 'a -> 'a t -> 'a t
      val remove : key -> 'a t -> 'a t
      val map : ('a -> 'b) -> 'a t -> 'b t
      val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
      val iter : (key -> 'a -> unit) -> 'a t -> unit
      val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
      val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
      val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
      val is_empty : 'a t -> bool
      val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
      val show : (Format.formatter -> 'a -> unit) -> 'a t -> string
    end
