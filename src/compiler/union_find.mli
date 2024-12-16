(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util.Util

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

module Make (M : Map.S) : S with type key = M.key and type t = M.key M.t
