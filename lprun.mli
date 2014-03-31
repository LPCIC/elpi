module Subst : sig
  type subst
  val empty : int -> subst
  val print_subst : subst -> string
  val print_substf : Format.formatter -> subst -> unit
  val apply_subst : subst -> Lpdata.LP.data -> Lpdata.LP.data
  val apply_subst_goal : subst -> Lpdata.LP.goal -> Lpdata.LP.goal
  val refresh_uv : int -> subst -> Lpdata.LP.data -> Lpdata.LP.data
end
module Red : sig
  val whd : Subst.subst -> Lpdata.LP.data -> Lpdata.LP.data * Subst.subst
end
exception UnifFail of string lazy_t
val unify : Lpdata.LP.data -> Lpdata.LP.data -> Subst.subst -> Subst.subst
exception NoClause
val run : Lpdata.LP.program -> Lpdata.LP.goal -> Subst.subst
