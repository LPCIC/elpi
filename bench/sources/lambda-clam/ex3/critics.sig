/* 

File: critics.sig
Author: Louise Dennis / James Brotherston
Description: Types for Critics
Last Modified: 13th August 2002

*/

sig critics.

accum_sig plan.
accum_sig method.

kind	action	       type.

type general_critic theory.

% Criticals

type 	fail_crit	crit.
type	id_crit		crit.
type	orelse_crit	crit -> crit -> crit.
type	cond_crit	(plan_state -> o) -> crit -> crit -> crit.
type 	try_crit	crit -> crit.
type	repeat_crit	crit -> crit.
type	then_crit	crit -> crit -> crit.

type 	subplan_crit	(list int) -> crit -> crit.
type	some_crit	(_ -> crit) -> crit.

type	user_crit	string -> crit.

type 	pop_critic	(list int) -> crit.
type	open_node	crit.
type	continue_crit	(meth -> meth) -> crit.
type 	roll_back_to_crit	meth -> (list int) -> crit.

% Actions

type critique	crit -> (list int) -> action.
type addmeth (list int) -> (list (list int)) -> action.
type endplan action.

type atomic_critic theory -> crit -> (list int) -> agenda -> o -> o -> (list changed_node)  -> agenda -> o.
type compound_critic theory -> crit -> crit -> o.

end
