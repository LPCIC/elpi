open Lpdata

module Extern : sig
  
  val abort : string -> Subst.subst -> Subst.subst
  val exit : string -> Subst.subst -> 'a
  
  val print : LP.data -> Subst.subst -> Subst.subst
  val printl : LP.data L.t -> Subst.subst -> Subst.subst

  val trace_counter : string -> LP.data -> Subst.subst -> Subst.subst
  val incr : string -> Subst.subst -> Subst.subst
  val get : string -> LP.data -> Subst.subst -> Subst.subst
  val reset : string -> Subst.subst -> Subst.subst

  val parse : string -> LP.data -> Subst.subst -> Subst.subst
  val read : LP.data -> Subst.subst -> Subst.subst

  val telescope : LP.data -> LP.data -> Subst.subst -> Subst.subst

end

val register_std : unit -> unit

val check_list : string -> LP.data -> LP.data L.t
val check_list2 : string -> LP.data -> LP.data * LP.data
