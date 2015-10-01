/* 

File: pretty_printer.mod
Author: James Brotherston / Louise Dennis
Description: Interface to the pretty printer
Last Modified: 15th August 2002

*/

module pretty_printer.

accumulate print_syntax, print_plan, print_open_math.
accum_sig  print_syntax, print_plan, print_open_math.


%% Commands for prompting the user in step-by-step mode

plan_step_prompts Plan Command:-
	interactive_mode Interaction,
	plan_step_for_b Interaction IP,
	IP Plan Command.

%% Local auxiliary declarations

local plan_step_for_b   interaction -> ((list changed_node) -> o -> o) -> o.
local command_plan_step_prompt_b (list changed_node) -> o -> o.
local xb_plan_step_prompt (list changed_node) -> o -> o.

plan_step_for_b command command_plan_step_prompt_b.
plan_step_for_b command_pretty command_plan_step_prompt_b.
plan_step_for_b xbarnacle xb_plan_step_prompt.

command_plan_step_prompt_b Plan Command:-	
	for_each Plan (X\ sigma Y\ sigma A\ (X = (add_node A Y), pprint_plan Y)),
	pprint_string "\n",
	pprint_string "Continue Planning?:",
        pprint_string "lclam:",	
	read Command.

xb_plan_step_prompt Plan continue:-	
	for_each Plan (X\ sigma Y\ sigma A\ (X = (add_node A Y), pprint_plan Y)).

pprint_method_failure Method _ Address:-
	interactive_mode xbarnacle,
	xbmode In Out, !,
	output Out "tree_clear_node_from_prolog {",
	term_to_string Address AString,
	output Out AString,
	output Out "} \nXB_END\n", !.
pprint_method_failure Method trueGoal _Adresss:-
	pprint_string "branch closed failed", !.
pprint_method_failure Method (_ ** _) _Adresss:-
	pprint_string "conjunction split failed", !.
pprint_method_failure Method (allGoal _ _) _Adresss:-
	pprint_string "allGoal to meta-level failed", !.
pprint_method_failure Method (existsGoal _ _) _Adresss:-
	pprint_string "allGoal to meta-level failed", !.
pprint_method_failure Method _ _Adresss:-
	pprint_string "failed", !.

pprint_method_success Method Goal Address:-
	interactive_mode xbarnacle,
	xbmode In Out, !,
	pprint_name Address,
	output Out "plan_update_planned_node assp {",
	term_to_string Address AString,
	output Out AString,
	output Out "} {",
	term_to_string Method MString,
	output Out MString,
	output Out "} open_status {",
	xb_pprint_goal Out Goal,
	output Out "} {",
	xb_pprint_goal Out Goal,
	output Out "} {",
	xb_pprint_goal Out Goal,
	output Out "}\nXB_END\n", !.
pprint_method_success Method trueGoal Address:-
	pprint_string "Branch closed!\n", !.
pprint_method_success Method (_ ** _) Address:-
	pprint_string "Splitting goal conjunction", 
	pprint_string "succeeded\n", !.
pprint_method_success Method (allGoal _ _) Address:-
	pprint_string "Moving allGoal to meta-level", 
	pprint_string "succeeded\n", !.
pprint_method_success Method (existsGoal _ _) Address:-
	pprint_string "Moving existsGoal to meta-level", 
	pprint_string "succeeded\n", !.
pprint_method_success Method Goal Address:-
	print "Method application:  ", pprint_name Method,
	pprint_string "succeeded\n", !.


%% Clauses for print commands which are dependent on the output mode

maybe_pprint_goal Goal:-
	super_silent off, !, pprint_goal Goal.
maybe_pprint_goal Goal:- !.

maybe_pprint_method_attempt Method Goal Address:-
	verbose on, !, 
	pprint_string "Attempting... ", pprint_name Method,
	on_backtracking 
              (pprint_method_failure Method Goal Address).
maybe_pprint_method_attempt M G A:- !.

maybe_pprint_backtracking Method Goal:-
	verbose on, !,
	on_backtracking 
	    (pprint_string "backtracking over",
		 ((compound_goal Goal, pprint_goal Goal);
		  ((Goal = (_ ** _), pprint_goal Goal);
		  ((not (compound_goal Goal)), pprint_name Method)))).
maybe_pprint_backtracking M G:- !.

end