/*

File: part_plan.sig
Author: Louise Dennis / James Brotherston
Description: Partial Planner (with Critics).
Last Modified: 16th August 2002

*/

sig part_plan.

accum_sig pds_support.

type dvar osyn.

type part_planner plan_state -> (action -> plan_state -> plan_state -> o) -> plan_state -> o.
	
end
