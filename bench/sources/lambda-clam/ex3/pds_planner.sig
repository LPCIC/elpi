 /*

File: pds_planner.sig
Author: Louise Dennis / James Brotherston
Description: Persistant Data Structure Planner (with Critics).
Last Modified: 16th August 2002

*/

sig pds_planner.

accum_sig pds_support.

type pds_planner plan_state -> (action -> plan_state -> plan_state -> o) -> plan_state -> o.

type pds_iter_planner plan_state -> (action -> plan_state -> plan_state -> o) -> plan_state -> o.

type iter_deep_planner plan_state -> (action -> plan_state -> plan_state -> o) -> plan_state -> int -> o.

type context_planner action -> agenda -> (action -> plan_state -> plan_state -> o) -> cplan -> int -> o.

end