/* 

File: print_syntax.mod
Author: Louise Dennis / James Brotherston
Description: pretty printing for term
Last Modified: 15th August 2002

*/

module print_syntax.

accumulate prettify, interaction.

%% Local declarations (pretty printing for specific interaction modes)

local pprint_syn_for         interaction -> (osyn -> o) -> o.
local pprint_name_for        interaction -> (A -> o) -> o.
local pprint_rewrite_for     interaction -> (direction -> osyn -> osyn -> osyn -> o) -> o.
local pprint_subst_for       interaction -> (subst -> o) -> o.
local pprint_goal_for        interaction -> (goal -> o) -> o.
local pprint_name_list_for   interaction -> ((list A) -> o) -> o.
local pprint_methodical_for  interaction -> (meth -> o) -> o.
local pprint_predicate_for   interaction -> (o -> o) -> o.
local pprint_tactic_for      interaction -> (tactic -> o) -> o.
local pprint_string_for      interaction -> (string -> o) -> o.

local command_pprint_rewrite direction -> osyn -> osyn -> osyn -> o.
local command_pprint_string  string -> o.

%% 
%% Catchall predicate for printing unprocessed to std_out followed by a newlien
%%

printstdout Term:-
	printterm std_out Term, print "\n".

%%
%%  TERMS
%%

pprint_term Term:-
	interactive_mode Interaction,
	pprint_syn_for Interaction Predicate,
	Predicate Term.

%% Using a variable means this acts as a default.
pprint_syn_for command_pretty (X\ (pretty_show_term X, print "\n")):-!.
%pprint_syn_for open_math (X\ (print_open_math X XString, print XString, print "\n")):-!.
pprint_syn_for _ printstdout.

%%
%% Theories
%%

pprint_name Theory:-
	interactive_mode Interaction,
	pprint_name_for Interaction Predicate,
	Predicate Theory.

pprint_name_for _ printstdout.

%%
%% Addresses and plan depth
%%

pprint_address Address Depth:-
	print "ADDRESS: ", pprint_name Address,
        print "DEPTH  : ", pprint_name Depth, print "\n".

%%
%% Goals
%%

pprint_goal Goal:-
	interactive_mode Interaction,
	pprint_goal_for Interaction Predicate,
	Predicate Goal, !.

%pprint_goal_for open_math open_math_show_goal.
pprint_goal_for command_pretty pretty_show_goal:- pprint_string "GOAL:", !.
pprint_goal_for xbarnacle (xb_pprint_goal Stream):-!.
pprint_goal_for _ printstdout.

xb_pprint_goal std_out Goal:-printstdout Goal, !.
xb_pprint_goal Out Goal:-
	term_to_string Goal GString,
	output Out GString.

%%
%% Rewrite Rules
%%

pprint_rewrite_rule Dir L R C:-
	interactive_mode Interaction,
	pprint_rewrite_for Interaction Predicate,
	Predicate Dir L R C.

pprint_rewrite_for _ command_pprint_rewrite.

command_pprint_rewrite _ L R C:-
	printstdout L,
	printstdout R,
	printstdout C.

command_pprint_rewrite Dir L R C:-
	printstdout Dir,
	printstdout L,
	printstdout R,
	printstdout C.

%%
%% Lists of names of things (e.g. rewrite rules)
%%
	
pprint_name_list List:-
	interactive_mode Interaction,
	pprint_name_list_for Interaction Predicate,
	Predicate List.

pprint_name_list_for _ printstdout.


%%
%% Substitutions
%%

pprint_subst Subst:-
	interactive_mode Interaction,
	pprint_subst_for Interaction Predicate,
	Predicate Goal.

pprint_subst_for _ printstdout.


%%
%% Methodicals
%%

pprint_methodical_for _ printstdout.

pprint_methodical Methodical:-
	interactive_mode Interaction,
	pprint_methodical_for Interaction Predicate,
	Predicate Methodical.

pprint_methodical_for _ printstdout.

%%
%% Pre and Post conditions
%%

pprint_predicate P:-
	interactive_mode Interaction,
	pprint_predicate_for Interaction Predicate,
	Predicate P.

pprint_predicate_for _ printstdout.

%%
%% Tactics
%%

pprint_tactic Tactic:-
	interactive_mode Interaction,
	pprint_tactic_for Interaction Predicate,
	Predicate Tactic.

pprint_tactic_for _ printstdout.


%%
%% Strings
%%

pprint_string String:-
	interactive_mode Interaction,
	pprint_string_for Interaction Predicate,
	Predicate String.

pprint_string_for _ command_pprint_string.

command_pprint_string String:-	
	print String, print "\n".

end
