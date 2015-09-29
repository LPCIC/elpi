/*

File: lclam_syntax.mod
Author: James Brotherston
Description: Syntax for plans, methods, critics, goals, rewrites etc.
Last Modified: 14th August 2002.

*/

module lclam_syntax.

accumulate goal, syntax, critics, lclam_utils.

/* Predicates for querying various rewrite lists */

sym_eval_rewrites_list L :-
	sym_eval_list L, !.

sym_eval_list nil.

general_rewrites_list L :-
	general_list L, !.

general_list nil.

lemma_rewrites_list L :-
	user_lemma_list L, !.

user_lemma_list nil.

defn_rewrites_list L :-
	user_defn_list L, !.

user_defn_list nil.

end
