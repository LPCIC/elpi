/* 

File: print_plan.mod
Author: Louise Dennis / James Brotherston
Description: Pretty printing for plans
Last Modified: 9th September 2002

*/

module print_plan.

%% Local auxiliary declarations

local pprint_for          interaction -> (plan -> o) -> o.
local pprint_cplan_for    interaction -> (cplan -> o) -> o.

local xb_pprint_plan      plan -> o.
local xb_print_cplan      out_stream -> cplan -> o.
local xb_print_goal_bit   out_stream -> goal -> (list cplan) -> o.

local pprint_text_cplan   cplan -> o.


/* Pretty printing for concise plans */

pprint_cplan CPlan:-
	interactive_mode Interaction,
	pprint_cplan_for Interaction Predicate,
	Predicate CPlan.

pprint_cplan_for command_pretty (x\ (pprint_text_cplan x)):-
	plan_printing_switch on, pprint_string "PROOF PLAN:\n", !.
pprint_cplan_for _ (x\ (printstdout x)):-
	plan_printing_switch on, !.
pprint_cplan_for _ (x\ (print "Plan found (not displayed) ...\n")).


pprint_text_cplan eplan:- pprint_string "NIL".

pprint_text_cplan (c_and_node Goal Address Meth Cs):-
	pprint_string "AND_NODE:",
	print "ADDRESS: ", pprint_name Address,
	pprint_goal Goal,
	print "METHOD:  ", pprint_name Meth,
	pprint_string "\n",
	for_each_cut Cs pprint_text_cplan.
	
pprint_text_cplan (c_forall_node Address F):-
	pprint_string "FORALL_NODE:",
	print "ADDRESS: ", pprint_name Address,
	pi z\ (pprint_text_cplan (F z)).

pprint_text_cplan (c_exists_node Address F):-
	pprint_string "EXISTS_NODE",
	print "ADDRESS: ", pprint_name Address,
	sigma z\ (pprint_text_cplan (F z)).
	






/* Pretty printing for verbose plans (currently unused) */

pprint_plan Plan:-
	pprint_string "Printing verbose plan",
	interactive_mode Interaction,
	pprint_for Interaction Predicate,
	Predicate Plan.

pprint_for xbarnacle xb_pprint_plan.
pprint_for _ printstdout.



/* Pretty printing of plans for XBarnacle (currently unused) */
/*
xb_pprint_plan Plan:-
	c_print_plan Plan CPlan,
	xbmode In Out,
	xb_print_cplan Out CPlan, !.

xb_print_cplan Out (c_and_node Goal Address Meth Children):-
	output Out "\nplan_create_child_node assp {",
	term_to_string Address AString,
	output Out AString,
	output Out "} open_status {",
	xb_pprint_goal Out Goal,
	output Out "} {",
	xb_pprint_goal Out Goal,
	output Out "} {",
	output Out "}\nXB_END\n", 
	for_each Children (xb_print_cplan Out), !.
xb_print_cplan Out (c_forall_node Address AtoPlan):-
	output Out "\nplan_create_child_node assp {",
	term_to_string Address AString,
	output Out AString,
	output Out "} open_status goal goal goal\nXB_END\n", 
	pi x\
		(for_each (AtoPlanList x) (xb_print_cplan Out)).
xb_print_cplan Out (c_exists_node Address AtoPlan):-
	output Out "\nplan_create_child_node assp {",
	term_to_string Address AString,
	output Out AString,
	output Out "} open_status goal goal goal\nXB_END\n", 
	(for_each (AtoPlanList X) (xb_print_cplan Out)).
*/

end

