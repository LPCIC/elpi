module type M = sig
  include Hashtbl.HashedType

  val pp : Format.formatter -> t -> unit
  val compare : t -> t -> int
end

module Make : functor (M : M) -> sig
  type opened [@@deriving show]
  type closed [@@deriving show]

  val roots : opened -> M.t list
  val create : unit -> opened
  val create_close : unit -> closed

  val add : opened -> M.t -> unit
  (** add an singleton in the disjoint set *)

  val find : opened -> M.t -> M.t
  val union : opened -> M.t * M.t -> unit

  val do_close : opened -> closed
  (** close a opened disjoint-set *)

  val do_open : closed -> opened
  (** clone a closed disjoint-set and open it  *)

  val merge : closed -> closed -> closed
  (** merges two disjoint-sets *)

  val union_c : closed -> M.t * M.t -> unit
  val pp : Format.formatter -> closed -> unit
end
