open Lpdata

exception UnifFail of string lazy_t
val unify : LP.data -> LP.data -> Subst.subst -> Subst.subst

(* Runtime *)
exception NoClause
val run : LP.program -> LP.goal -> Subst.subst
