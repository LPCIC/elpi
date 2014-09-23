(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Lpdata

(* out of place *)
val uniq : LP.data list -> LP.data list

exception NOT_A_PU (* for debuggin only *)

exception UnifFail of string lazy_t
val unify : ?depth:int -> LP.data -> LP.data -> Subst.subst -> Subst.subst

(* Runtime *)
exception NoClause

type continuation
type result =
 LP.goal * LP.data list * Subst.subst *
  (LP.goal * LP.program) list * continuation

val run_dls : LP.program -> LP.goal -> result
val next: continuation -> result

(* as run_dls, with simplified output, used only for debugging *)
val run : LP.program -> LP.goal -> LP.goal * Subst.subst


type objective =
  [ `Atom of LP.data * LP.key
  | `Unify of LP.data * LP.data
  | `Custom of string * LP.data
  | `Cut
  | `Context of LP.data
  | `Delay of LP.data * LP.premise * LP.data option * LP.data option
  | `Resume of LP.data * LP.premise
  | `Unlock of LP.data
  ]
type context = LP.data option list
type goal = context * objective * LP.program * LP.program * int
type dgoal = LP.data * LP.premise * context * LP.program * int
type goals = goal list * dgoal list * LP.program
type alternatives = (Subst.subst * goals) list

val goals_of_premise : LP.program -> LP.clause -> context -> LP.program -> int -> Subst.subst -> goal list * Subst.subst

val register_custom_predicate :
  string -> (LP.data -> Subst.subst -> Subst.subst) -> unit

val register_custom_control_operator :
  string -> (LP.data -> Subst.subst -> goals -> alternatives -> Subst.subst * goals * alternatives) -> unit
