(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Lpdata

exception UnifFail of string lazy_t
val unify : LP.data -> LP.data -> Subst.subst -> Subst.subst

(* Runtime *)
exception NoClause

type continuation
type result = LP.goal * (LP.data * LP.data) list * Subst.subst * LP.goal list * continuation

val run_dls : LP.program -> LP.goal -> result
val next: continuation -> result

(* as run_dls, with simplified output, used only for debugging *)
val run : LP.program -> LP.goal -> LP.goal * Subst.subst

(* debug *)
val prepare_initial_goal : LP.goal -> LP.goal * Subst.subst

val register_custom :
  string -> (LP.data -> Subst.subst -> int -> LP.program -> Subst.subst) -> unit
