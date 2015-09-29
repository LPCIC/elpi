/*

File: plan.mod
Author: Louise Dennis / James Brotherston
Description: Predicates supporting PDS plan structure
Last Modified: 10th September 2002

*/

module plan.

local nobinder osyn.

%% support for context
pplan_node _ emptyPlan.
retrieve_node Address Plan:-
	pplan_node Address P, !,
	%% delay unification until after the cut to make sure _only_ the
	%% last plan node succeeds
	(Plan = P).
address_binder _ nobinder.
retrieve_binder Address Binder:-
	address_binder Address B, !,
	(Binder = B).


%%%%%%%%%%%%%%%%%%
%% transform_node
%% Applies a function at a given address in a plan.
%%%%%%%%%%%%%%%%%%
transform_node PlanA nil F PlanB:-
	F PlanA PlanB.
transform_node (forall_node Ad Type AtoPlan) (1::Address) F 
               (forall_node Ad Type Plan):-
	pi z\ (transform_node (AtoPlan z) Address F (Plan z)).
transform_node (exists_node Ad Type AtoPlan) (1::Address) F 
               (exists_node Ad Type Plan):-
	pi Z\ (transform_node (AtoPlan Z) Address F (Plan Z)).

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Working with preconditions
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%

success_pre nil _:- fail.
success_pre ((success (P, Precondition))::_) P.
success_pre ((success (P, Precondition))::T) POut:-
	success_pre ((success Precondition)::T) POut.
success_pre ((success Precondition)::T) Precondition.
success_pre (_::T) P:-
	success_pre T P.


failed_pre nil _:- fail.
failed_pre ((failed P)::_) P.
failed_pre (_::T) POut:-
	failed_pre T POut.

%% Plan support predicates 

get_preconditions Ad Pre:-
	retrieve_node Ad Node,
	(Node = (and_node G Ad C M Pre T)).
get_address (and_node G Ad C M Pre T) Ad.
get_address (forall_node Ad _ _) Ad.
get_address (exists_node Ad _ _) Ad.

get_goal Ad G:-
	retrieve_node Ad Node,
	(Node = (and_node G Ad C M Pre T)).
get_continuation Ad C:-
	retrieve_node Ad Node,
	(Node = (and_node G Ad C M Pre T)).

update_continuation C Ad (and_node G Ad C M Pre T):-
	retrieve_node Ad Node,
	(Node = (and_node G Ad _ M Pre T)).

get_method Ad Meth:-
	retrieve_node Ad Node,
	(Node = (and_node _ _ _ Meth _ _)).


%% Put an address at the front of the agenda

push_agenda Address (active_agenda List) (active_agenda (Address::Rest)):-
	memb_and_rest Address List Rest, !.
push_agenda Address (active_agenda List) (active_agenda (Address::List)).
	


end
