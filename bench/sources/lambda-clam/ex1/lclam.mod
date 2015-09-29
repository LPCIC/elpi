/* 

File: lclam.mod
Author: Louise Dennis / James Brotherston
Description: Top Level Loop for lclam
Last Modified: 21st August 2002

*/

module lclam.

accumulate theory_db, planner.

lclam:- pprint_acks, std_lclam.

pprint_acks:- 
	pprint_string "This is Lambda-CLAM v4.0.0",
	pprint_string "Copyright (C) 2002 Mathematical Reasoning Group, University of Edinburgh",
	pprint_string "NOTE: this program uses the MRG patched version of Teyjus 1.0-b33.\n\n".


std_lclam:-
	(interactive_mode command; interactive_mode command_pretty;
	 interactive_mode open_math),
	pprint_string "lclam:", !,
	read Command, 
	execute_command Command std_lclam.

std_lclam:- 
	interactive_mode sock_read_write,
        lclam_sockets (lclam_server_socket In Out) _,
	printstdout In,
	printstdout Out,
	on_backtracking (printstdout "backtracking out of read_token"),
	read_token In Command,
	printstdout Command,
	string_to_term Command Term,
	printstdout Term,
	execute_command Term std_lclam, !.

testloop (H, T):- !,
	execute_command H (testloop T).
testloop H:- !,
	execute_command H lclam.

execute_command halt _ :- halt.
execute_command quit _.

% command to undo the last (undoable) command.  Works best with ProofGeneral

execute_command undo _ :- 
   pprint_string "Undoing last command (ignore failed message below)", 
   !, fail.

% command to automatically generate a directed lemma from a goal

execute_command (qed ReasonType Goal) Loop:-
   goal_to_lemma ReasonType Goal Theory Name Dir Cond Lhs Rhs,
   execute_command (add_lemma Theory Name Dir Cond Lhs Rhs) Loop.

% commands to control verbosity of output
% silent mode suppresses failed method applications and backtracking
% super-silent mode suppresses goal printing

execute_command (verbose_mode) Loop:-
	((verbose_m on, silent_m off, super_silent_m off) => 
	 (pprint_string "Verbose mode: on", Loop)).

execute_command (silent_mode) Loop:-
	((verbose_m off, silent_m on, super_silent_m off) => 
	 (pprint_string "Silent mode: on", Loop)).

execute_command (super_silent_mode) Loop:-
	((verbose_m off, silent_m on, super_silent_m on) => 
	 (pprint_string "Super-silent mode: on", Loop)).

% commands to add / remove a spypoint

execute_command (set_spypoint Meth) Loop:-
	(spypoint_m on Meth => (pprint_string "Spypoint set to: ", pprint_name Meth, Loop)). 

execute_command (remove_spypoint Meth) Loop:-
	(spypoint_m off Meth => (pprint_string "Spypoint removed: ", pprint_name Meth, Loop)).

% commands from version 3.0.0

execute_command (plan_printing X) Loop:-
	(plan_printing_switch X => (pprint_string "Done", Loop)).

execute_command (step_by_step X) Loop:-
	(step_by_step_m X => (pprint_string "Done", Loop)).

execute_command (interaction_mode X) Loop:-
	(interactive X => (pprint_string "Done", Loop)).

execute_command (add_osyn Theory Syntax Type) Loop:-
	(has_otype Theory Syntax Type => (pprint_string "Done", Loop)).

execute_command (add_atomic Theory Name Goal Pre Post Out Tac) Loop:-
	(atomic Theory Name Goal Pre Post Out Tac => (pprint_string "Done", Loop)).
execute_command (add_compound Theory Name Meth Ad Pre) Loop:-
	(compound Theory Name Meth Ad Pre => (pprint_string "Done", Loop)).

execute_command (add_definition Theory Name C L R) Loop:-
	(definition Theory Name C L R => (pprint_string "Done", Loop)).
execute_command (add_axiom Theory Name Dir C L R) Loop:-
	(axiom Theory Name Dir C L R => (pprint_string "Done", Loop)).
execute_command (add_lemma Theory Name Dir C L R) Loop:-
	(lemma Theory Name Dir C L R => 
         (print "Lemma added to context: ", pprint_name Name, Loop)).

execute_command (add_query Theory Query Hyps Conc) Loop:-
	(top_goal Theory Query Hyps Conc => (pprint_string "Done", Loop)).




execute_command (add_theory Theory) Loop :-
	print "Trying ...",
	use_thy Theory As,
	assert_all As (pprint_string "Done", Loop).


assert_all nil Loop :- (pprint_string "Done", Loop).
assert_all ((has_otype Th X T)::As) Loop  :- 
	(has_otype Th X T) => (assert_all As Loop).
assert_all ((atomic Theory Name Goal Pre Post Out Tac)::As) Loop :- 
	(atomic Theory Name Goal Pre Post Out Tac) => (assert_all As Loop).
assert_all ((axiom Theory Name Dir C L R)::As) Loop :- 
	(axiom Theory Name Dir C L R) => (assert_all As Loop).
assert_all ((top_goal Theory Name Hs C)::As) Loop :- 
	(top_goal Theory Name Hs C) => (assert_all As Loop).
assert_all ((definition Theory Name C L R)::As) Loop :- 
	(definition Theory Name C L R) => (assert_all As Loop).


/*
kind assert type.

type assert_all2 (list assert) -> o -> o.

type assertion o -> assert.

assert_all2 [] Loop :- (pprint_string "Assertions added", Loop).
assert_all2 ((assertion A)::As) Loop:- A => (assert_all2 As Loop).
*/


execute_command (add_scheme Theory Scheme Type Subst Osyn GoalIn GoalOut) Loop:-
	(induction_scheme Theory Scheme Type Subst Osyn GoalIn GoalOut => (pprint_string "Done", Loop)).


%% Commands for manipulating the symbolic evaluation list

execute_command (add_to_sym_eval_list RewriteRules) Loop:-
	sym_eval_rewrites_list L,
	append RewriteRules L NewL,
	(sym_eval_list NewL => (pprint_string "Done", Loop)).
execute_command (delete_from_sym_eval_list nil) Loop:- (pprint_string "Done", Loop).
execute_command (delete_from_sym_eval_list (H::T)) Loop:-
	sym_eval_rewrites_list L,
	nth L _ H Rest,
	(sym_eval_list Rest => (execute_command (delete_from_sym_eval_list T) Loop)).
execute_command (set_sym_eval_list RewriteRules) Loop:-
	(sym_eval_list RewriteRules => (pprint_string "Done", Loop)).


execute_command (add_theory_to_sym_eval_list Theory) Loop:-
	findall (RR\ sigma L\ sigma R\ sigma Cond\ definition Theory RR L R Cond) DefList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ axiom Theory RR Dir L R Cond) AxList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ lemma Theory RR Dir L R Cond) LemList,
	append DefList Axlist Tmp,
	append Tmp LemList List,
	execute_command (add_to_sym_eval_list List) Loop.
execute_command (add_theory_defs_to_sym_eval_list Theory) Loop:-
	findall (RR\ sigma L\ sigma R\ sigma Cond\ definition Theory RR L R Cond) DefList,
	execute_command (add_to_sym_eval_list DefList) Loop.
execute_command (delete_theory_from_sym_eval_list Theory) Loop:-
	findall (RR\ sigma L\ sigma R\ sigma Cond\ definition Theory RR L R Cond) DefList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ axiom Theory RR Dir L R Cond) AxList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ lemma Theory RR Dir L R Cond) LemList,
	append DefList Axlist Tmp,
	append Tmp LemList List,
	execute_command (delete_from_sym_eval_list List) Loop.
execute_command (set_theory_sym_eval_list Theory) Loop:-
	findall (RR\ sigma L\ sigma R\ sigma Cond\ definition Theory RR L R Cond) DefList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ axiom Theory RR Dir L R Cond) AxList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ lemma Theory RR Dir L R Cond) LemList,
	append DefList Axlist Tmp,
	append Tmp LemList List,
	execute_command (set_sym_eval_list List) Loop.


%% Commands for manipulating the general rewriting list

execute_command (add_to_rewrite_list RewriteRules) Loop:-
	general_rewrites_list L,
	append RewriteRules L NewL,
	(general_list NewL => (pprint_string "Done", Loop)).
execute_command (delete_from_rewrite_list nil) Loop:- (pprint_string "Done", Loop).
execute_command (delete_from_rewrite_list (H::T)) Loop:-
	general_rewrites_list L,
	nth L _ H Rest,
	(general_list Rest => (execute_command (delete_from_rewrite_list T) Loop)).
execute_command (set_rewrite_list RewriteRules) Loop:-
	(general_list RewriteRules => (pprint_string "Done", Loop)).
execute_command (add_theory_to_rewrite_list Theory) Loop:-
	findall (RR\ sigma L\ sigma R\ sigma Cond\ definition Theory RR L R Cond) DefList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ axiom Theory RR Dir L R Cond) AxList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ lemma Theory RR Dir L R Cond) LemList,
	append DefList Axlist Tmp,
	append Tmp LemList List,
	execute_command (add_to_rewrite_list List) Loop.
execute_command (delete_theory_from_rewrite_list Theory) Loop:-
	findall (RR\ sigma L\ sigma R\ sigma Cond\ definition Theory RR L R Cond) DefList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ axiom Theory RR Dir L R Cond) AxList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ lemma Theory RR Dir L R Cond) LemList,
	append DefList Axlist Tmp,
	append Tmp LemList List,
	execute_command (delete_from_rewrite_list List) Loop.
execute_command (set_theory_rewrite_list Theory) Loop:-
	findall (RR\ sigma L\ sigma R\ sigma Cond\ definition Theory RR L R Cond) DefList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ axiom Theory RR Dir L R Cond) AxList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ lemma Theory RR Dir L R Cond) LemList,
	append DefList Axlist Tmp,
	append Tmp LemList List,
	execute_command (set_rewrite_list List) Loop.


%% Commands for manipulating the wave rule list

execute_command (add_to_wave_rule_list RewriteRules) Loop:-
	wave_rules_list L,
	append RewriteRules L NewL,
	(wave_rule_list NewL => (pprint_string "Done", Loop)).
execute_command (delete_from_wave_rule_list nil) Loop:- (pprint_string "Done", Loop).
execute_command (delete_from_wave_rule_list (H::T)) Loop:-
	wave_rules_list L,
	nth L _ H Rest,
	(wave_rule_list Rest => (execute_command (delete_from_wave_rule_list T) Loop)).
execute_command (set_wave_rule_list RewriteRules) Loop:-
	(wave_rule_list RewriteRules => (pprint_string "Done", Loop)).
execute_command (add_theory_to_wave_rule_list Theory) Loop:-
	findall (RR\ sigma L\ sigma R\ sigma Cond\ definition Theory RR L R Cond) DefList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ axiom Theory RR Dir L R Cond) AxList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ lemma Theory RR Dir L R Cond) LemList,
	append DefList Axlist Tmp,
	append Tmp LemList List,
	execute_command (add_to_wave_rule_list List) Loop.
execute_command (add_theory_defs_to_wave_rule_list Theory) Loop:-
	findall (RR\ sigma L\ sigma R\ sigma Cond\ definition Theory RR L R Cond) DefList,
	execute_command (add_to_wave_rule_list DefList) Loop.
execute_command (delete_theory_from_wave_rule_list Theory) Loop:-
	findall (RR\ sigma L\ sigma R\ sigma Cond\ definition Theory RR L R Cond) DefList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ axiom Theory RR Dir L R Cond) AxList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ lemma Theory RR Dir L R Cond) LemList,
	append DefList Axlist Tmp,
	append Tmp LemList List,
	execute_command (delete_from_wave_rule_list List) Loop.
execute_command (set_theory_wave_rule_list Theory) Loop:-
	findall (RR\ sigma L\ sigma R\ sigma Cond\ definition Theory RR L R Cond) DefList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ axiom Theory RR Dir L R Cond) AxList,
	findall (RR\ sigma Dir\ sigma L\ sigma R\ sigma Cond\ lemma Theory RR Dir L R Cond) LemList,
	append DefList Axlist Tmp,
	append Tmp LemList List,
	execute_command (set_wave_rule_list List) Loop.


%% Commands for manipulating the induction scheme list

execute_command (add_to_induction_scheme_list Schemes) Loop:-
	induction_schemes_list L,
	append Schemes L NewL,
	(induction_schemes_list_ NewL => (pprint_string "Done", Loop)).
execute_command (delete_from_induction_scheme_list nil) Loop:- (pprint_string "Done", Loop).
execute_command (delete_from_induction_scheme_list (H::T)) Loop:-
	induction_schemes_list L,
	nth L _ H Rest,
	(induction_schemes_list_ Rest => (execute_command (delete_from_induction_scheme_list T) Loop)).
execute_command (set_induction_scheme_list Scheme) Loop:-
	(induction_schemes_list_ Scheme => (pprint_string "Done", Loop)).
execute_command (add_theory_to_induction_scheme_list Theory) Loop:-
	findall (Scheme\ sigma Type\ sigma Subst\ sigma Osyn\ sigma GI\ sigma GO\ induction_scheme Theory Scheme Type Subst Osyn GI GO) List,
	execute_command (add_to_induction_scheme_list List) Loop.
execute_command (delete_theory_from_induction_scheme_list Theory) Loop:-
	findall (Scheme\ sigma Type\ sigma Subst\ sigma Osyn\ sigma GI\ sigma GO\ induction_scheme Theory Scheme Type Subst Osyn GI GO) List,
	execute_command (delete_from_induction_scheme_list List) Loop.
execute_command (set_theory_induction_scheme_list Theory) Loop:-
	findall (Scheme\ sigma Type\ sigma Subst\ sigma Osyn\ sigma GI\ sigma GO\ induction_scheme Theory Scheme Type Subst Osyn GI GO) List,
	execute_command (set_induction_scheme_list List) Loop.

execute_command (set_wave_rule_to_sym_eval) Loop:-
	sym_eval_rewrites_list L,
	execute_command (set_wave_rule_list L) Loop.


%% Commands for manipulating the user lemma list

execute_command (add_to_user_lemma_list Lemmas) Loop:-
	lemma_rewrites_list L,
	check_lemmas Lemmas,
 	pprint_string "Lemmas found",
	append Lemmas L NewL,
	(user_lemma_list NewL => (pprint_string "Done", Loop)).
execute_command (delete_from_user_lemma_list nil) Loop:- (pprint_string "Done", Loop).
execute_command (delete_from_user_lemma_list (H::T)) Loop:-
	lemma_rewrites_list L,
	nth L _ H Rest,
	(user_lemma_list Rest => (execute_command (delete_from_user_lemma_list T) Loop)).
execute_command (set_user_lemma_list Lemmas) Loop:-
	check_lemmas Lemmas,
	pprint_string "Lemmas found",
	(user_lemma_list Lemmas => (pprint_string "Done", Loop)).

local check_lemmas (list rewrite_rule) -> o.
check_lemmas [].
check_lemmas (H::T):- 
   lemma _Th H _Dir _Cond _Lhs _Rhs, 
   check_lemmas T.
check_lemmas X:- pprint_string "Couldn't find lemmas", !, fail.

%% Commands for manipulating the user definition list

execute_command (add_to_user_defn_list Defns) Loop:-
	defn_rewrites_list L,
	check_defns Defns,
	pprint_string "Definitions found",
	append Defns L NewL,
	(user_defn_list NewL => (pprint_string "Done", Loop)).
execute_command (delete_from_user_defn_list nil) Loop:- (pprint_string "Done", Loop).
execute_command (delete_from_user_defn_list (H::T)) Loop:-
	defn_rewrites_list L,
	nth L _ H Rest,
	(user_defn_list Rest => (execute_command (delete_from_user_defn_list T) Loop)).
execute_command (set_user_defn_list Defns) Loop:-
	check_defns Defns,
	pprint_string "Definitions found",
	(user_defn_list Defns => (pprint_string "Done", Loop)).

local check_defns (list rewrite_rule) -> o.
check_defns []:- !.
check_defns (H::T):- 
   definition _Th H _Cond _Lhs _Rhs, 
   check_defns T.
check_defns X:- pprint_string "Couldn't find defns", !, fail.

%% Miscellaneous commands

execute_command (mw_close) Loop:-
	close_connection, !,
	halt.
execute_command reset_lclam Loop:-
	(induction_schemes_list_ [] =>
	(sym_eval_list [] =>
	(general_list [] =>
	(wave_rule_list [] =>
	(user_lemma_list [] =>
	(user_defn_list [] =>
	(pprint_string "All rule lists reset.", Loop))))))).

execute_command Command Loop:-
	not (Command = (add_theory T)),
	print "default\n", Command,  !,
	Loop.
execute_command Command Loop:-
	not (Command = (add_theory T)),
	pprint_string "  Failed.\n",
	Loop.




end



