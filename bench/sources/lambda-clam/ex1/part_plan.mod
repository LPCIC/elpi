/*

File: part_plan.mod
Author: Louise Dennis / James Brotherston
Description: Partial Planner (with Critics).
Last Modified: 9th September 2002

*/

module part_plan.

local partial_planner_nodes action -> (list changed_node) -> agenda -> (action  -> plan_state -> plan_state -> o) -> cplan -> int -> o.
local goallist (list goal) -> cplan.
local partial_planner action -> agenda -> (action -> plan_state -> plan_state -> o) -> cplan -> int -> o.

%% Context planner which does most of the actual planning work

part_planner (pstate Agenda Plan) AP (cpstate finished_agenda PlanOut):-
	(pplan_node nil Plan =>
		partial_planner (addmeth nil nil) Agenda AP PlanOut -1), !,
	printstdout PlanOut.

partial_planner _ (active_agenda nil) _AP  (goallist nil) DepthLimit:- 
	pprint_string "reached empty agenda\n".

partial_planner Action (active_agenda (H::T)) AP (goallist (G::PlanOut)) DepthLimit:- 
	retrieve_node H K,
	(K = (and_node G H Continuation Meth Pre Tac)),
	pds_method_trans G Continuation id_meth id_meth,
	partial_planner Action (active_agenda T) AP (goallist PlanOut) DepthLimit.

partial_planner Action (active_agenda (H::T)) AgendaPredicate PlanOut DepthLimit:-
	retrieve_node H K,
	(K = (and_node Goal H (then_meth (cut_meth M) L) Meth Pre Tac)),
        ((pplan_node H (and_node Goal H (then_meth M L) Meth Pre Tac)) =>
        partial_planner Action (active_agenda (H::T)) AgendaPredicate PlanOut DepthLimit).

partial_planner ActionIn Agenda AgendaPredicate PSOut DepthLimit:-
	context_plan_step ActionIn ActionOut Agenda AgendaOut 
                          NewNodes Spy DepthLimit,
	%% Critics may radically modify current agenda by removing nodes
	%% so use agenda out.
	create_agenda ActionOut (pliststate AgendaOut NewNodes) 
		AgendaPredicate (pliststate NewAgenda NewNewNodes) Spy,
        partial_planner_nodes ActionOut NewNewNodes NewAgenda AgendaPredicate PSOut DepthLimit.


%%%  "Asserting" the new nodes
partial_planner_nodes Action nil A AP PSOut DL:-
	partial_planner Action A AP PSOut DL. 
partial_planner_nodes Action ((add_node Ad (and_node Gi Ad Mi Ci Pi Tai)::T)) A AP 
	PSOut DL:-
	((pplan_node Ad (and_node Gi Ad Mi Ci Pi Tai)) => 
		partial_planner_nodes Action T A AP PSOut DL).
partial_planner_nodes Action ((add_node Ad (forall_node Ad Type AtoPlan))::T) A AP (PSOut dvar) DL:-
	pi x\ (
		((pplan_node Ad (forall_node Ad Type AtoPlan)) => 
		  ((address_binder Ad x) => (partial_planner_nodes Action ((add_node (1::Ad) (AtoPlan x))::T) A AP (PSOut x) DL)))).
partial_planner_nodes Action ((add_node Ad (exists_node Ad Type AtoPlan))::T) A AP PSOut DL:-
	((pplan_node Ad (exists_node Ad Type AtoPlan)) => 
	  ((address_binder Ad Wit) => 
		partial_planner_nodes Action ((add_node (1::Ad) (AtoPlan Wit))::T) A AP PSOut DL, printstdout "witness:", printstdout Wit)).
partial_planner_nodes Action ((delete_node Ad)::T) A AP PSOut DL:-
	((pplan_node Ad emptyPlan =>
		partial_planner_nodes Action T A AP PSOut DL)).
	
end
