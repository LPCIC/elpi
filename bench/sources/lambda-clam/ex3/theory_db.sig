/*

File: theory_db.sig
Author: Louise Dennis / James Brotherston
Description: Predicate to make theories simulate a database.
Last Modified: 21st August 2002

*/

sig theory_db.

accum_sig wave_critics.

type query_osyn theory -> osyn -> osyn -> o.
type query_top_goal theory -> query -> o.
type query_rewrite_rule theory -> rewrite_rule -> o.
type query_induction_scheme theory -> scheme -> o.
type query_sym_eval_list o.
type query_general_rewrites_list o.
type query_induction_scheme_list o.
type query_wave_rule_list o.
type query_method theory -> meth -> o.

end