/*

File: planner.mod
Author: Louise Dennis / James Brotherston
Description: Top Level Management of Planners.
Last Modified: 9th September 2002

*/

module planner.

%% Import planners and supporting functions

accumulate pds_planner, part_plan, pds_support.

%% Import pretty printer and syntax utility functions

accumulate pretty_printer, lclam_syntax.

%% Import sockets module

accumulate sockets.

%%%%%%%%%%%%%%%%%%
%% Wrapper to run any planner etc. etc.
%%%%%%%%%%%%%%%%%%

pds_plan Method Query:-
	plan_this pds_planner Method Query depth_first_plan Plan.

pds_iter_plan Method Query:-
	plan_this pds_iter_planner Method Query depth_first_plan Plan.

%% JB: The Claudio planners are identical to their standard equivalents 
%%     except that they return the plan state as a variable binding.

claudio_plan Method Query Plan:-
	plan_this pds_planner Method Query depth_first_plan PlanState,
	PlanState = (cpstate _ Plan).

claudio_iter_plan Method Query Plan:-
	plan_this pds_iter_planner Method Query depth_first_plan PlanState,
	PlanState = (cpstate _ Plan).


plan_this Proof_planner Method Query AgendaPredicate Plan:-
	top_goal _ Query Hyps Osyn, !,
	announce_start Query Osyn,
	Proof_planner (pstate (active_agenda [nil]) 
	  (and_node (seqGoal (Hyps >>> Osyn))
		     nil
		     Method
		     nomethodyet
		     []
		     notacticyet))
	  AgendaPredicate
	  Plan, !,
%	  printstdout "hello",
	((Plan = (pstate _ VerbosePlan), !, pprint_plan VerbosePlan);
	(Plan = (cpstate _ CPlan), pprint_cplan CPlan)),
	announce_end, !.

local announce_start query -> osyn -> o.
local announce_end o.

announce_end:-
	interactive_mode sock_read_write,
	lclam_sockets (lclam_server_socket _ Out) _,
	pprint_string "sending result",
	output Out "Plan Succeeded\x80",
	flush Out.

announce_end:-
	xbmode In Out, !,
	output Out "\nplan_update_proof_plan\nXB_END\n".
announce_end:-
	pprint_string "Plan Succeeded".

announce_start Query GoalConc:-
	xbmode In Out, !,
	term_to_string Query QString,
	output Out "\nmisc_switch_query ",
	output Out QString,
	output Out "\nXB_END\n",
	output Out "\nplan_new_query ",
	output Out QString,
	output Out "\nXB_END\n",
	output Out "plan_update_planned_node assp nil null open_status {",
	term_to_string GoalConc GCString,
	output Out GCString,
	output Out "} {",
	output Out GCString,
	output Out "} {",
	output Out GCString,
	output Out "}\nXB_END\n", !.
announce_start Query _:-
	term_to_string Query QString,
	pprint_string "Planning: ",
	pprint_string QString.
	


end
