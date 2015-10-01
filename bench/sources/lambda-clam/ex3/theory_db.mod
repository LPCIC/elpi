/*

File: theory_db.mod
Author: Louise Dennis / James Brotherston
Description: Predicates to make theories simulate a database.
Last Modified: 21st August 2002

*/

module theory_db.

accumulate wave_critics.

query_osyn Theory Osyn Type:-
	has_otype Theory Osyn Type,
	pprint_name Theory,
	pprint_term Osyn,
	pprint_term Type.

query_top_goal Theory Goal:-
	top_goal Theory Goal Hyps Conc,
	pprint_name Theory,
	for_each Hyps pprint_term,
	pprint_string ">>>",
	pprint_term Conc.

query_rewrite_rule Theory Rule:-
	definition Theory Rule C L R,
	pprint_string "Definition:",
	pprint_name Theory,
	pprint_rewrite_rule _ C L R.

query_rewrite_rule Theory Rule:-
	axiom Theory Rule Dir C L R,
	pprint_string "Axiom:",
	pprint_name Theory,
	pprint_rewrite_rule Dir C L R.

query_rewrite_rule Theory Rule:-
	lemma Theory Rule Dir C L R,
	pprint_string "Lemma:",
	pprint_name Theory,
	pprint_rewrite_rule Dir C L R.

query_induction_scheme Theory Scheme:-
	induction_scheme Theory Scheme Type Subst Syn GoalIn GoalOut,
	pprint_name Theory,
	pprint_term Type,
	pprint_subst Subst,
	pprint_term Syn,
	pprint_goal GoalIn,
	pprint_goal GoalOut.

query_sym_eval_list:-
	sym_eval_list L,
	pprint_name_list L.

query_general_rewrites_list:-
	general_rewrites_list L,
	pprint_name_list L.

query_induction_scheme_list:-
	induction_schemes_list L,
	pprint_name_list L.

query_wave_rule_list:-
	wave_rules_list L,
	pprint_name_list L.

query_method Theory Meth:-
	compound Theory Meth Methodical _ Preconditions,
	pprint_string "Compound method:",
	pprint_name Theory,
	pprint_methodical Methodical,
	pprint_predicate Preconditions.

query_method Theory Meth:-
	atomic Theory Meth Input Preconditions Postconditions Output Tactic,
	pprint_string "Atomic method:",
	pprint_name Theory,
	pprint_goal Input,
	pprint_predicate Preconditions,
	pprint_predicate Postconditions,
	pprint_goal Output,
	pprint_tactic Tactic.

end
