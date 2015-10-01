/*

File: plan.sig
Author: Louise Dennis / James Brotherston
Description: Plan Types
Last Modified: 10th September 2002

*/

sig plan.

accum_sig basic_types, lclam_utils.

kind plan type.
kind agenda type.
kind plan_state type.
kind preconditions type.
kind changed_node type.


%% PRECONDITION CONSTRUCTORS

type success o -> preconditions.
type failed  o -> preconditions.
type failed_pre (list preconditions) -> o -> o.
type success_pre (list preconditions) -> o -> o.
type nopreconditions preconditions.

%% PLAN CONSTRUCTORS

type emptyPlan plan.

/*
A plan node is an 6-tuple of 
1. a goal, 
2. address, 
3. a method continuation, 
4. a method (the one applied at that node) 
5. its preconditions, 
6. the tactic attached to the node. 
*/

type and_node goal -> (list int) -> meth -> meth -> (list preconditions) -> tactic -> plan.
type or_node goal -> (list int) -> meth -> meth -> (list preconditions) -> tactic -> plan.

type exists_node (list int) -> osyn -> (A -> plan) -> plan.
type forall_node (list int) -> osyn -> (A -> plan) -> plan.

%% AGENDA CONSTRUCTORS

type finished_agenda agenda.
type active_agenda (list (list int)) -> agenda.
type failed_agenda (list (list int)) -> agenda.

type push_agenda (list int) -> agenda -> agenda -> o.


%% PLAN STATE CONSTRUCTORS

type pstate agenda -> plan -> plan_state.
type pliststate agenda -> (list changed_node) -> plan_state.

%% CONTEXT PLANNING SUPPORT
type pplan_node (list int) -> plan -> o.
type retrieve_node (list int) -> plan -> o.
type address_binder (list int) -> osyn -> o.
type retrieve_binder (list int) -> osyn -> o.

%% CHANGENODE CONSTRUCTORS
type add_node (list int) -> plan -> changed_node.
type delete_node (list int) -> changed_node.

%% PREDICATES FOR FETCHING AND TRANSFORMING PLAN NODES

type transform_node plan -> (list int) -> (plan -> plan -> o) -> plan -> o.


%% Predicates for fetching information from and updating plan nodes.

type get_preconditions (list int) -> (list preconditions) -> o.
type get_address plan -> (list int) -> o.
type get_goal (list int) -> goal -> o.
type get_continuation (list int) -> meth -> o.
type update_continuation meth -> (list int) -> plan -> o.
type get_method (list int) -> meth -> o.

end