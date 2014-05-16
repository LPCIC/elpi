(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Lpdata

exception UnifFail of string lazy_t
val unify : LP.data -> LP.data -> Subst.subst -> Subst.subst

(* Runtime *)
exception NoClause
val run_dls : LP.program -> LP.goal -> LP.goal * Subst.subst * LP.goal list
val run : LP.program -> LP.goal -> LP.goal * Subst.subst

(* debug *)
val prepare_initial_goal : LP.goal -> LP.data list * LP.goal * Subst.subst

val register_custom :
  string -> (LP.data -> Subst.subst -> int -> LP.program -> Subst.subst) -> unit

val ctx_of_hv : LP.data list -> LP.name list
