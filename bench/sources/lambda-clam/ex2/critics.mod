/* 

File: critics.mod
Author: Louise Dennis / James Brotherston
Description: Support for Critics
Last Modified: 9th September 2002

*/

module critics.

accumulate plan.
accumulate method.

local nearest_occurence meth -> (list int) -> (list int) -> o.
local create_delete_list (list int) -> (list changed_node) -> o.
local create_delete_list_n (list int) -> int -> (list changed_node) -> o.
local remove_from_agenda (list changed_node) -> agenda -> agenda -> o.


atomic_critic general_critic (pop_critic H)
	_
	Agenda
	(Agenda = (active_agenda (H::_T)))
	true
	nil
	Agenda.

atomic_critic general_critic open_node
	Address
	Agenda
	true
	(retrieve_node Address PlanNode,
	 push_agenda Address Agenda NewAgenda)
	((add_node Address PlanNode)::nil)
	NewAgenda.

atomic_critic general_critic (roll_back_to_crit Meth Ad)
	Address
	Agenda
	(nearest_occurence Meth Ad Address,
	 retrieve_node Ad (and_node G Ad C _ _ _),
	 create_delete_list Ad DeleteList,
	 append DeleteList ((add_node Ad (and_node G Ad C _ _ _))::nil) ChangeList)
	%% Putting the added node at the end since the deletelist will delete
	%% it first.
	(remove_from_agenda DeleteList Agenda NewAgenda,
	 push_agenda Ad NewAgenda AgendaOut)
	ChangeList
	AgendaOut.

atomic_critic general_critic (continue_crit C)
	Address
	Agenda
	true
	(get_continuation Address Cont,
	 keep_variables_free Cont NewCont, 
 	 update_continuation (C NewCont) Address NewPlan,
	 push_agenda Address Agenda NewAgenda)
	((add_node Address NewPlan)::nil)
	NewAgenda.

%% Finding the nearest previous occurence of a given method.
nearest_occurence Meth Address Address:-
	get_method Address Meth, !.
nearest_occurence Meth Ad (H::T):-
	nearest_occurence Meth Ad T.

create_delete_list Ad nil:-
	retrieve_node Ad emptyPlan, !.
create_delete_list Ad ((delete_node Ad)::DL):-
	retrieve_node Ad Plan,
	create_delete_list_n Ad 1 DL.

create_delete_list_n Add N nil:-
	create_delete_list (N::Add) nil, !.
create_delete_list_n Add N DLOut:-
	create_delete_list (N::Add) DL,
	N1 is (N + 1),
	create_delete_list_n Add N1 DL2,
	append DL DL2 DLOut.

remove_from_agenda nil Agenda Agenda.
remove_from_agenda ((delete_node Ad)::DL) (active_agenda Agenda) NewAgenda:-
	(memb_and_rest Ad Agenda Rest; Rest = Agenda), !,
	remove_from_agenda DL (active_agenda Rest) NewAgenda.
	

end
