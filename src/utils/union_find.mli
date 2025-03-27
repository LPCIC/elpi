(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Util

module type S = sig
  include Show
  include ShowKey
  module KeySet : Util.Set.S with type elt = key

  val empty : t
  val is_empty : t -> bool
  val find : t -> key -> key
  val find_class : t -> key -> key * KeySet.t
  val union : t -> key -> canon:key -> key option * t
  val merge : t -> t -> t
  val roots : t -> KeySet.t
  (* The first higher-order function should be injective otherwise the UF is broken *)
  val mapi : (key -> key) -> t -> t 
end

module Make (O : Map.OrderedType) : S with type key = O.t
