/*

File: plan_support.mod
Author: Louise Dennis / James Brotherston
Description: Persistant Data Structure Planner (with Critics).
Last Modified: 10th September 2002

*/

module plan_support.

accumulate switch.

%%%%%%%%%%%%%%%%%%
/*
TIDYING CONTINUATIONS.
The schemes for generating continuations generate a lot of unwanted
then_meth idmeth s which confuse the algorithms later in the code.  This 
code attempts to tidy up the continuation.
*/
%%%%%%%%%%%%%%%%%%%

tidy_continuation (repeat_meth id_meth) id_meth:-
	!.
tidy_continuation (repeat_meth M) (repeat_meth Out):-
	!, tidy_continuation M Out, !.

tidy_continuation (then_meth id_meth M) M1 :- !,
	tidy_continuation M M1, !.
tidy_continuation (then_meth M1 M2) (then_meth M1P M2P) :-
	!, tidy_continuation M1 M1P,
	tidy_continuation M2 M2P, !.

tidy_continuation (then_meths id_meth M2) MOut :- !,
	tidy_continuation M2 MOut, !.
tidy_continuation (then_meths M1 M2) (then_meths M1P M2P) :-
	!, tidy_continuation M1 M1P,
	tidy_continuation M2 M2P, !.

tidy_continuation (orelse_meth id_meth _M2) id_meth :-!.
tidy_continuation (orelse_meth M1 M2) (orelse_meth M1P M2P) :- !,
	tidy_continuation M1 M1P,
	tidy_continuation M2 M2P, !.

tidy_continuation (try_meth id_meth) id_meth :- !.
tidy_continuation (try_meth M) (try_meth M1) :- !,
	tidy_continuation M M1, !.

tidy_continuation (cond_meth C M1 M2) (cond_meth C M1P M2P):- !,
	tidy_continuation M1 M1P,
	tidy_continuation M2 M2P, !.

tidy_continuation (complete_meth M) M1 :-
	!, tidy_continuation M M1, !.

tidy_continuation (map_meth M) (map_meth M1):-
	!, tidy_continuation M M1, !.

tidy_continuation (pair_meth M1 M2) (pair_meth M1P M2P):-!,
	tidy_continuation M1 M1P,
	tidy_continuation M2 M2P, !.

tidy_continuation (cut_meth M) (cut_meth M1):-
	!, tidy_continuation M M1, !.

tidy_continuation M M:-!.


%%%%%%%%%%%%%%%%%%%%
%% METHOD APPLICATION
%%%%%%%%%%%%%%%%%%%%

apply_method_to_goal (addmeth _  _) (patch_meth M Critic) Goal NewGoals ((success Preconditions)::nil):-
	(not (M = triv_meth)),
	(not (M = id_meth)), 
	atomic _ M Goal Preconditions Postconditions NewGoals Tactic,
	Preconditions,
	Postconditions.

apply_method_to_goal (critique Critic _) (patch_meth M Critic) Goal NewGoals Pr:-
	(not (M = triv_meth)),
	(not (M = id_meth)), !,
	atomic _ M Goal Preconditions Postconditions NewGoals Tactic,
	evaluate_in_turn Preconditions Pr 0.


apply_method_to_goal (addmeth _ _) M Goal NewGoals ((success Preconditions)::nil):-
	(not (M = triv_meth)),
	(not (M = id_meth)), !,
	atomic _ M Goal Preconditions Postconditions NewGoals Tactic,
	Preconditions,
	Postconditions.



expand_compound_method M Methodical Preconditions Address:-
	(not (M = triv_meth)),
	(not (M = id_meth)), 
	compound _ M Methodical Address Preconditions,
	Preconditions, !.



%%%%%%%%%%%%%%%%%%%%%%
%% evaluate_in_turn
%% Pseudo-interpreter for method preconditions
%%%%%%%%%%%%%%%%%%%%%%

local evaluate_in_turn o -> (list preconditions) -> int -> o.

evaluate_in_turn (H, T) ((success H)::Tout) Out:-
	(not (H = (_, _))),
	H,
	pprint_name H, pprint_string "success\n",
	evaluate_in_turn T Tout Out.
evaluate_in_turn (H, T) ((failed H)::Tout) 0:-
	(not (H = (_, _))),
	(not H),
	pprint_name H,
	pprint_string "failed\n",
	evaluate_in_turn T Tout _.
evaluate_in_turn Pre ((success Pre)::nil) 1:-
	(not (Pre = (_, _))),
	Pre, pprint_name Pre, pprint_string "success\n".
evaluate_in_turn Pre ((failed Pre)::nil) 0:-
	(not (Pre = (_, _))),
	pprint_name Pre, pprint_string "failed\n",
	(not Pre).

%%%%%%%%%%%%%%%%%%%%%%%
%% create_agenda
%% Agenda Creation
%%%%%%%%%%%%%%%%%%%%%%%	

%% JB: final argument of create_agenda refers to spypoint status

create_agenda Action PlanState AP NewPlanState off:-
	step_by_step_mode off, !,
	AP Action PlanState NewPlanState, !.
create_agenda Action (pliststate OldAgenda Plans) AP NPS off:-
	step_by_step_mode on, !,
	plan_step_prompts Plans Continue_or_Intervene,
	modify_agenda Continue_or_Intervene Action (pliststate OldAgenda Plans) AP NPS, !.
create_agenda Action (pliststate OldAgenda Plans) AP NPS on:-
	plan_step_prompts Plans Continue_or_Intervene,
	modify_agenda Continue_or_Intervene Action (pliststate OldAgenda Plans) AP NPS, !.

local modify_agenda o -> action -> plan_state -> (action -> plan_state -> plan_state -> o) -> plan_state -> o.

modify_agenda continue Action PS AP NPS:-
	AP Action PS NPS, !.
modify_agenda abandon _ (pliststate _ P) _ (pliststate (active_agenda nil) P) :- !.
modify_agenda backtrack _ _ _ _ :- !, fail.
modify_agenda (plan_node Address) Action PS AP (pliststate (active_agenda (Address::NewAgenda)) NewPlan):-
	AP Action PS (pliststate (active_agenda NAgenda) NewPlan),
	memb_and_rest Address NAgenda NewAgenda, !.
modify_agenda (plan_node _) Action (pliststate Agenda Plan) AP NPS:-
	pprint_string "Sorry incorrect address selected",
	plan_step_prompts Plan Continue_or_Intervene,
	modify_agenda Continue_or_Intervene Action (pliststate Agenda Plan) AP NPS, !.

modify_agenda (try M) Action PS AP (pliststate (active_agenda (H::NewAgenda)) NewPlan):-
	print "a\n",
	AP Action PS (pliststate (active_agenda (H::NewAgenda)) NPlan),
	print "b\n",
	((memb_and_rest (add_node Ad Plan) NPlan Rest,
		append Route N Ad,
	%% A bit convoluted - we want to modify one of the new nodes if
	%% it is next on the agenda - but the new nodes can be composite
	%% of forall_nodes and and_nodes etc.  They don't get properly
	%% flattened out until context_planner_nodes.
	%% 
	%% As a result we need to use transform_node to alter them _but_
	%% transform_node expects to navigate from the "top" of the plan
	%% and follow the given address to the appropriate node.  As we
	%% are starting part way into a plan we simulate this by adapting
	%% the address (using the append statement above) so that it is
	%% now the address of the desired node relative to the top of the
	%% subplan.
	  transform_node Plan Route
            (X\ Y\ 
		sigma Goal\ sigma H\ sigma Cont\ sigma Meth\ sigma Pre\ 
		sigma Tac\ sigma NewCont\ sigma C\
        (X = (and_node Goal H Cont Meth Pre Tac),
	 add_method M Cont NewCont, 
        (Y = (and_node Goal H NewCont Meth Pre Tac))))
            NwPlan, !,
	append Rest ((add_node Ad NwPlan)::nil) NewPlan);
	(retrieve_node H 
		(and_node Goal H Cont Meth Pre Tac),
	  add_method M Cont NewCont, 
	  append NPlan ((add_node H (and_node Goal H NewCont Meth Pre Tac))::nil) NewPlan)).


%%%%%%%%%%%%%%%%%%
/*
ADDING a Method into a Methodical Continuation
*/
%%%%%%%%%%%%%%%%%%%

local add_method meth -> meth -> meth -> o.

add_method M (repeat_meth M1) (then_meth (try_meth M) (repeat_meth M1)) .

add_method M (then_meth M1 M2) (then_meth M1P M2):-
	add_method M M1 M1P.

add_method M (then_meths M1 M2) (then_meth (try_meth M) (then_meths M1 M2)).

add_method M (orelse_meth M1 M2) (then_meth (try_meth M) (orelse_meth M1 M2)).

add_method M (try_meth M1) (then_meth (try_meth M) (try_meth M1)).
add_method M (cut_meth M1) (then_meth (try_meth M) (cut_meth M1)).

add_method M (cond_meth C M1 M2) (then_meth (try_meth M) (cond_meth C M1 M2)).

add_method M (complete_meth M1) (complete_meth M2) :-
	!, add_method M M1 M2.

add_method M (map_meth M1) (map_meth M2):-
	!, add_method M M1 M2.

add_method M (pair_meth M1 M2) (pair_meth M3 M2):-
	!, add_method M M1 M3.

add_method M1 M (then_meth (try_meth M1) M).

%%%%%%%%%%%%%%%%%%%%%%%%
%% depth_first_plan
%% Simple agenda function
%%%%%%%%%n%%%%%%%%%%%%%%%

depth_first_plan (addmeth H NewAds) (pliststate (active_agenda T) Plan) 
			    (pliststate (active_agenda NewAddresses) Plan):-
	memb_and_rest H T Rest,
	append NewAds Rest NewAddresses.
depth_first_plan (addmeth H NewAds) (pliststate (active_agenda T) Plan) 
			    (pliststate (active_agenda NewAddresses) Plan):-
	(not (member H T)),
	append NewAds T NewAddresses.
depth_first_plan (critique C H) (pliststate (active_agenda (H::T)) Plan) (pliststate (active_agenda (H::T)) Plan).


end
