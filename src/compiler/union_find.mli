open Elpi_util.Util

(* module type M = sig
  include Hashtbl.HashedType

  val pp : Format.formatter -> t -> unit
  val compare : t -> t -> int
end

module Make1 : functor (M : M) -> sig
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
end *)

module type S = sig
  include Show
  include ShowKey

  val empty : t
  val is_empty : t -> bool
  val find : t -> key -> key
  val union : t -> key -> key -> key option * t
  val merge : t -> t -> t
  val roots : t -> key list
end

module Make (M : Elpi_util.Util.Map.S) : S with type key = M.key and type t = M.key M.t
