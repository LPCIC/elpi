/*

File: method.mod
Author: Louise Dennis / James Brotherston
Description: Predicate for constructing copies of a method
Last Modified: 13th August 2002

*/

module method.

%%%%%%%%%%%%%%%%%%%%%%%%%%
%% change_method_vars
%% mostly this just copies a method - however some methods which take a 
%% variable argument intended for instantiation by the method have 
%% dedicated clauses for change_method_vars to handle this properly.
%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Using change_method_vars predicate to introduce new meta_variables for any 
%% that might be in M.

%% The base case for this appears in pds_planner.mod - after all the cases
%% that appear in theory files.

change_method_vars (cond_meth C M1 M2) (cond_meth C M1P M2P) :-
	print "Cond_meth\n",
	!, keep_variables_free M1 M1P,
	keep_variables_free M2 M2P.

change_method_vars (then_meth M1 M2) (then_meth L M2P):-
	!, keep_variables_free M1 L,
	keep_variables_free M2 M2P.

change_method_vars (then_meths M1 M2) (then_meths L M2P):-
	!, keep_variables_free M1 L,
	keep_variables_free M2 M2P.

change_method_vars (orelse_meth M1 M2) (orelse_meth L M2P):-
	!, keep_variables_free M1 L,
	keep_variables_free M2 M2P.

change_method_vars (pair_meth M1 M2) (pair_meth L M2P):-
	!, keep_variables_free M1 L,
	keep_variables_free M2 M2P.

change_method_vars (complete_meth M) (complete_meth M1):-
	!, keep_variables_free M M1.
change_method_vars (try_meth M) (try_meth M1):-
	!, keep_variables_free M M1.
change_method_vars (map_meth M) (map_meth M1):-
	!, keep_variables_free M M1.
change_method_vars (cut_meth M) (cut_meth M1):-
	!, keep_variables_free M M1.
change_method_vars (repeat_meth M) (repeat_meth M1):-
	!, keep_variables_free M M1.

%% Special clause for patch_meth
change_method_vars (patch_meth M C) (patch_meth M1 C):-
	!, change_method_vars M M1.

keep_variables_free M M1:-
	change_method_vars M M1.
keep_variables_free M M.

end