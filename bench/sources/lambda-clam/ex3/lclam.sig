/* 

File: lclam.sig
Author: Louise Dennis / James Brotherston
Description: Top Level Loop for lclam
Last Modified: 21st August 2002

*/

sig lclam.

accum_sig theory_db, planner.

type lclam o.
type std_lclam o.
type pprint_acks o.
type execute_command o -> o -> o.


%% Commands
type qed reasontype -> query -> o.
type undo o.
type quit o.
type reset_lclam o.
type step_by_step switch -> o.
type plan_printing switch -> o.
type set_spypoint meth -> o.
type remove_spypoint meth -> o.
type verbose_mode o.
type silent_mode o.
type super_silent_mode o.
type interaction_mode interaction -> o.

type add_osyn theory -> osyn -> osyn -> o.
type add_atomic theory -> meth -> goal -> o -> o -> goal -> tactic -> o.
type add_compound theory -> meth -> meth -> (list int) -> o -> o.
type add_definition theory -> rewrite_rule -> osyn -> osyn -> osyn -> o.
type add_axiom theory -> rewrite_rule -> direction -> osyn -> osyn -> osyn -> o.
type add_lemma theory -> rewrite_rule -> direction -> osyn -> osyn -> osyn -> o.
type add_query theory -> query -> (list osyn) -> osyn -> o.

/* add_theory does not take a theory argument, since the theory is not yet
   defined, but a filename */

type add_theory string -> o.
type assert_all (list o) -> o -> o.

type add_scheme theory -> scheme -> osyn -> subst -> osyn -> goal -> goal -> o.

type add_to_sym_eval_list (list rewrite_rule) -> o.
type delete_from_sym_eval_list (list rewrite_rule) -> o.
type set_sym_eval_list (list rewrite_rule) -> o.
type add_theory_to_sym_eval_list theory -> o.
type add_theory_defs_to_sym_eval_list theory -> o.
type delete_theory_from_sym_eval_list theory -> o.
type set_theory_sym_eval_list theory -> o.

type add_to_rewrite_list (list rewrite_rule) -> o.
type delete_from_rewrite_list (list rewrite_rule) -> o.
type set_rewrite_list (list rewrite_rule) -> o.
type add_theory_to_rewrite_list theory -> o.
type delete_theory_from_rewrite_list theory -> o.
type set_theory_rewrite_list theory -> o.

type add_to_wave_rule_list (list rewrite_rule) -> o.
type delete_from_wave_rule_list (list rewrite_rule) -> o.
type set_wave_rule_list (list rewrite_rule) -> o.
type add_theory_to_wave_rule_list theory -> o.
type add_theory_defs_to_wave_rule_list theory -> o.
type delete_theory_from_wave_rule_list theory -> o.
type set_theory_wave_rule_list theory -> o.

type add_to_induction_scheme_list (list scheme) -> o.
type delete_from_induction_scheme_list (list scheme) -> o.
type set_induction_scheme_list (list scheme) -> o.
type add_theory_to_induction_scheme_list theory -> o.
type delete_theory_from_induction_scheme_list theory -> o.
type set_theory_induction_scheme_list theory -> o.

type set_wave_rule_to_sym_eval o.

type add_to_user_lemma_list (list rewrite_rule) -> o.
type delete_from_user_lemma_list (list rewrite_rule) -> o.
type set_user_lemma_list (list rewrite_rule) -> o.

type add_to_user_defn_list (list rewrite_rule) -> o.
type delete_from_user_defn_list (list rewrite_rule) -> o.
type set_user_defn_list (list rewrite_rule) -> o.

type mw_close o.
type reset_lclam o.

type benchmark_plan theory -> meth -> query -> o.
type testloop o -> o.

type use_thy  string -> list o -> o.

end



