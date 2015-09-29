/*

File: lclam_syntax.sig
Author: James Brotherston
Description: Syntax for plans, methods, critics, goals, rewrites etc.
Last Modified: 14th August 2002.

*/

sig lclam_syntax.

accum_sig ripple_types, goal, syntax, critics.

type sym_eval_rewrites_list (list rewrite_rule) -> o.
type sym_eval_list (list rewrite_rule) -> o.
type general_rewrites_list (list rewrite_rule) -> o.
type general_list (list rewrite_rule) -> o.
type lemma_rewrites_list (list rewrite_rule) -> o.
type user_lemma_list (list rewrite_rule) -> o.
type defn_rewrites_list (list rewrite_rule) -> o.
type user_defn_list (list rewrite_rule) -> o.
type wave_rules_list (list rewrite_rule) -> o.
type wave_rule_list (list rewrite_rule) -> o.

end
