/*

File: pds_planner.mod
Author: Louise Dennis / James Brotherston
Description: Persistant Data Structure Planner (with Critics).
             Depth First and Iterative Deepening flavours
Last Modified: 10th September 2002

*/

module pds_planner.

local context_planner_nodes action -> (list changed_node) -> agenda -> (action  -> plan_state -> plan_state -> o) -> cplan -> int -> o.


%%%%%%%%%%%%%%%%%%%
%% PDS ALGORITHM - NO CRITICS
%%%%%%%%%%%%%%%%%%%

%% JB: planners now call context_planner with an extra argument indicating 
%%     limit of depth-first search

%% DFS planner

pds_planner (pstate Agenda Plan) AP (cpstate finished_agenda PlanOut):-
	(pplan_node nil Plan =>
		context_planner (addmeth nil nil) Agenda AP PlanOut -1), !.


%% Iterative deepening planner
%% 3 is the initial depth limit
%% Depth limit is incremented in steps of 2

pds_iter_planner (pstate Agenda Plan) AP (cpstate finished_agenda PlanOut):-
	iter_deep_planner (pstate Agenda Plan) AP 
                          (cpstate finished_agenda PlanOut) 3.

iter_deep_planner (pstate Agenda Plan) AP (cpstate finished_agenda PlanOut) DepthLimit:-
	print "Calling context_planner with depth limit:",
	pprint_name DepthLimit, print "\n",
	(pplan_node nil Plan =>
	    context_planner (addmeth nil nil) Agenda AP PlanOut DepthLimit), !.

iter_deep_planner (pstate Agenda Plan) AP (cpstate finished_agenda PlanOut) DepthLimit:-
	pprint_string "Iteration completed\n",
	NewDepthLimit is DepthLimit + 2,
	iter_deep_planner (pstate Agenda Plan) AP (cpstate finished_agenda PlanOut) NewDepthLimit, !.


%% Context planner which does most of the actual planning work

context_planner _ (active_agenda nil) _AP PlanOut DepthLimit:- 
	pprint_string "reached empty agenda\n".
%% LD. Commented out - causes heap overflow with big benchmarks
%% maybe we should instigate some sort of flag so it isn't called in specific
%% cases but is called as a default???
% 	build_plan nil PlanOut.

context_planner Action (active_agenda (H::T)) AgendaPredicate PlanOut DepthLimit:-
	retrieve_node H K,
	(K = (and_node Goal H (then_meth (cut_meth M) L) Meth Pre Tac)),
        ((pplan_node H (and_node Goal H (then_meth M L) Meth Pre Tac)) =>
        context_planner Action (active_agenda (H::T)) AgendaPredicate PlanOut DepthLimit).

context_planner ActionIn Agenda AgendaPredicate PSOut DepthLimit:-
	context_plan_step ActionIn ActionOut Agenda AgendaOut 
                          NewNodes Spy DepthLimit,
	%% Critics may radically modify current agenda by removing nodes
	%% so use agenda out.
	create_agenda ActionOut (pliststate AgendaOut NewNodes) 
		AgendaPredicate (pliststate NewAgenda NewNewNodes) Spy,
        context_planner_nodes ActionOut NewNewNodes NewAgenda AgendaPredicate PSOut DepthLimit.


%%%  "Asserting" the new nodes
context_planner_nodes Action nil A AP PSOut DL:-
	context_planner Action A AP PSOut DL. 
context_planner_nodes Action ((add_node Ad (and_node Gi Ad Mi Ci Pi Tai)::T)) A AP 
	PSOut DL:-
	((pplan_node Ad (and_node Gi Ad Mi Ci Pi Tai)) => 
		context_planner_nodes Action T A AP PSOut DL).
context_planner_nodes Action ((add_node Ad (forall_node Ad Type AtoPlan))::T) A AP PSOut DL:-
	pi x\ (
		((pplan_node Ad (forall_node Ad Type AtoPlan)) => 
		  ((address_binder Ad x) => (context_planner_nodes Action ((add_node (1::Ad) (AtoPlan x))::T) A AP PSOut DL)))).
context_planner_nodes Action ((add_node Ad (exists_node Ad Type AtoPlan))::T) A AP PSOut DL:-
	((pplan_node Ad (exists_node Ad Type AtoPlan)) => 
	  ((address_binder Ad Wit) => 
		context_planner_nodes Action ((add_node (1::Ad) (AtoPlan Wit))::T) A AP PSOut DL, printstdout "witness:", printstdout Wit)).
context_planner_nodes Action ((delete_node Ad)::T) A AP PSOut DL:-
	((pplan_node Ad emptyPlan =>
		context_planner_nodes Action T A AP PSOut DL)).
	

end
