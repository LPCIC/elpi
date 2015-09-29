/*

File: pds_support.mod
Author: Louise Dennis / James Brotherston
Description: Persistant Data Structure Planner (with Critics).
Last Modified: 10th September 2002

*/

module pds_support.

accumulate plan_support.

local apply_critic_nodes (list changed_node) -> (list int) -> agenda -> crit -> action -> (list changed_node) -> agenda -> o.

local agenda_to_action agenda -> action -> o.
local build_child_nodes int -> (list int) -> (list cplan) -> o.


%%%%%%%%%%%%%%%%%
%% PDS ONE STEP PLANNER 
%%%%%%%%%%%%%%%%%%
%% One step of the planning process

context_plan_step (critique Critic Address) Action Agenda NewAgenda NewNodes Spypoint DepthLimit:-
	apply_critic nil Agenda Critic Action NewNodes NewAgenda, !.

context_plan_step (addmeth _ _) Action (active_agenda (Address::T)) (active_agenda (Address::T)) NewNodes Spypoint DepthLimit:-
	length Address Depth, Depth = DepthLimit,
	retrieve_node Address K,
	(K = (and_node Goal Address MethodIn M Pre Tactic)),
	((super_silent off, pprint_goal Goal, !) ; true),
	pprint_address Address Depth,
	pprint_string "Depth limit reached - backtracking\n", !, fail.

context_plan_step (addmeth _ _) Action (active_agenda (Address::T)) (active_agenda (Address::T)) NewNodes Spypoint DepthLimit:-
	%% We don't instantiate K immediately because we want to know the first
	%% success at that address.
	length Address Depth, (not (Depth = DepthLimit)), !,
	retrieve_node Address K,
	(K = (and_node Goal Address MethodIn M Pre Tactic)),
	maybe_pprint_goal Goal,
	pprint_address Address Depth,
	pds_method_trans Goal MethodIn Method Continuation,
	maybe_pprint_method_attempt Method Goal Address,
	tidy_continuation Continuation NewContinuation,
	apply_method_at_address Action Method NewContinuation Address NewNodes,
	maybe_pprint_backtracking Method Goal, 	
	pprint_method_success Method Goal Address, 
	check_spypoint Method Spypoint.

%% check if last successful method application is a spypoint

local check_spypoint meth -> switch -> o.

check_spypoint Method on:- spypoint_mode on Method.
check_spypoint _ off.


%% splitting up goal conjunctions
%% JB: use keep_variables_free to allow the two copies of the continuation
%% to use different metavariables

local apply_method_at_address action -> meth -> meth -> (list int) -> (list changed_node) -> o.

apply_method_at_address (addmeth Address [(1::Address), (2::Address)]) M Cont Address NewNodes:-
	retrieve_node Address K,
	(K = (and_node (G1 ** G2) Address C _M Pre T)),
	(M = (pair_meth M1 M2), keep_variables_free Cont Cont1, !,
	 NewNodes = [(add_node (1::Address) (and_node G1 (1::Address) (then_meth M1 Cont) nomethodyet nil notacticyet)), (add_node (2::Address) (and_node G2 (2::Address) (then_meth M2 Cont1) nomethodyet nil notacticyet))];
	 keep_variables_free C C1,
	 NewNodes = [(add_node (1::Address) (and_node G1 (1::Address) C nomethodyet nil notacticyet)),
(add_node (2::Address) (and_node G2 (2::Address) C1 nomethodyet nil notacticyet))]), !.

apply_method_at_address (addmeth Address [(1::Address)]) _M _Cont Address [(add_node Address (forall_node Address T (x\ (and_node (G x) (1::Address) Cont nomethodyet nil notacticyet))))]:-
	retrieve_node Address K,
	get_goal Address (allGoal T G),
	get_continuation Address Cont,
	!.

apply_method_at_address (addmeth Address [(1::Address)]) _ _ Address [(add_node Address (exists_node Address T (x\ (Out x))))]:-
	retrieve_node Address K,
	get_goal Address (existsGoal T G),
	get_continuation Address Cont,
	pi x\ ((Out x) = (and_node (G x) (1::Address) Cont nomethodyet nil notacticyet)),
	!.

%% Succeed if trueGoal reached
apply_method_at_address (addmeth Address nil) _ _ Address                         [(add_node Address (and_node trueGoal Address 
                          id_meth triv_meth
                          nil notacticyet))]:-
	retrieve_node Address K,
	(K = (and_node trueGoal Address _ _ _ _)), !.

%% Check triv_meth applied to a true goal
/* redundant?
apply_method_at_address (addmeth Address nil) triv_meth _ Address                       [(add_node Address (and_node trueGoal Address  
                          id_meth triv_meth
                          nil notacticyet))] :-
	retrieve_node Address K,
	(K = (and_node trueGoal Address _ _ _ _ _)), !.
*/

%% Two id_meths in a row imply proof plan failure (I think)
apply_method_at_address (addmeth Address Addresses) id_meth id_meth
	       _ _ :-
		!, fail.

%% id_meth encountered normally
apply_method_at_address (addmeth Address [Address]) id_meth Cont 
	       Address
	       [(add_node Address (and_node G Address Cont M Pre T))]:-
	%% Needed because of possible map_meth in Cont
	retrieve_node Address K,
	(K = (and_node G Address L M Pre T)).


%% atomic method application
apply_method_at_address Action M Cont Address ((add_node Address (and_node Goal Address C Meth NewPreconditions notacticyet))::Child):-
	retrieve_node Address K,
	(K = (and_node Goal Address C _  Pre _)),
	(M = (map_meth Meth); M = Meth),
 	apply_method_to_goal Action Meth Goal NewGoal P,
	append Pre P NewPreconditions,
	((Action = (addmeth Address [(1::Address)]), 
	Child = ((add_node (1::Address) (and_node NewGoal (1::Address) Cont nomethodyet nil notacticyet))::nil));
	 (Action = (critique _ Address), Child = nil)).


%% compound method application 
apply_method_at_address (addmeth Address (Address::nil)) M Cont Address 
                 [(add_node Address (and_node Goal Address 
                             (then_meth Methodical Cont) 
			     nomethodyet
                             NewPreconditions notacticyet))]:-
	retrieve_node Address K,
	(K = (and_node Goal Address C _ Pre _)),
	(M = (map_meth Meth); M = Meth),
	expand_compound_method Meth Methodical Preconditions Address,
	append Pre ((success Preconditions)::nil) NewPreconditions.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Critics Code
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% apply_critic +Critic +State -NewState 
% This evaluates compound critic definitions, and applies base critics.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

local apply_critic (list int) -> agenda -> crit -> action -> (list changed_node) -> agenda -> o.

apply_critic Address Agenda id_crit Action nil Agenda:-
	agenda_to_action Agenda Action.

apply_critic Ad Ag (orelse_crit C1 _) A NN AO:-
        apply_critic Ad Ag C1 A NN AO.

apply_critic Ad Ag (orelse_crit _ C2) A NN AO:-
        apply_critic Ad Ag C2 A NN AO.

apply_critic Ad Ag (cond_crit Cond C1 C2) A NN AO:-
        (((Cond State), !, C = C1) ; C = C2), !,
        apply_critic Ad Ag C A NN AO.
apply_critic Ad Ag (try_crit C) A NN AO:-
        apply_critic Ad Ag (orelse_crit C id_crit) A NN AO.

apply_critic Ad Ag (then_crit C1 C2) A NN AO:- !,
        apply_critic Ad Ag C1 _ NNI AO1,
        apply_critic_nodes NNI Ad AO1 C2 A NN2 AO,
	append NNI NN2 NN.

apply_critic Ad Ag (repeat_crit C) A NN AO:- !,
      apply_critic Ad Ag (then_crit C (orelse_crit (repeat_crit C) id_crit)) A NN AO.

apply_critic _ Agenda (subplan_crit Ad C) A NN AO:- !,
        apply_critic Ad Agenda C A NN AO.

apply_critic Ad Ag (some_crit C) A NN AO:- 
        C2 = (C _),
        apply_critic Ad Ag C2 A NN AO.

apply_critic Ad Ag C A NN AO:-
        compound_critic _ C CDef, !,
        apply_critic Ad Ag CDef A NN AO.

apply_critic Ad Ag C Action NN AO:-
	pprint_string "attempting atomic critic",
	pprint_name C,
        atomic_critic _ C Ad Ag Pre Eff NN AO,
        Pre,
        Eff,
	agenda_to_action AO Action,
	pprint_name C,
	pprint_string "suceeded\n".


%% Louise:  edited last T to nil following my files.
agenda_to_action (active_agenda (H::T)) (addmeth H (H::nil)).


%%%  "Asserting" the new nodes
apply_critic_nodes nil Ad Ag C A NN AO:-
	apply_critic Ad Ag C A NN AO.
apply_critic_nodes ((add_node Ad (and_node Gi Ad Mi Ci Pi Tai)::T)) Ad2 Ag C A NN AO:-
	((pplan_node Ad (and_node Gi Ad Mi Ci Pi Tai)) => 
		apply_critic_nodes T Ad2 Ag C A NN AO).
apply_critic_nodes ((add_node Ad (forall_node Ad Type AtoPlan))::T) Ad2 Ag C A NN AO:-
	pi x\ (
		((pplan_node Ad (forall_node Ad Type AtoPlan)) => 
		  ((address_binder Ad x) =>
			apply_critic_nodes ((add_node (1::Ad) (AtoPlan x))::T) Ad2 Ag C A NN AO))).
apply_critic_nodes ((add_node Ad (exists_node Ad Type AtoPlan))::T) Ad2 Ag C A N AO:-
	((pplan_node Ad (exists_node Ad Type AtoPlan)) => 
	  ((address_binder Ad Wit) => 
		apply_critic_nodes ((add_node (1::Ad) (AtoPlan Wit))::T) Ad2 Ag C A N AO)).
apply_critic_nodes ((delete_node Ad)::T) Ad2 Ag C A NN AO:-
	((pplan_node Ad emptyPlan) =>
		apply_critic_nodes T Ad2 Ag C A NN AO).
	

%%%%%%%%%%%%%%%%%%
/*
METHODICAL TRANSFORMATIONS for Planner as specified in BBNote 1349 but
with some additional clauses to try and help tidy up occurences of
id_meth
*/
%%%%%%%%%%%%%%%%%%%

pds_method_trans _ (repeat_meth id_meth) id_meth id_meth:-
	!.
%% Using keep_variables_free predicate to introduce new meta_variables for any 
%% that 
%% might be in M.
pds_method_trans G (repeat_meth M) F 
                 (then_meth L (orelse_meth (repeat_meth M1) id_meth)) :-
	keep_variables_free M M1,
	!, pds_method_trans G M F L.

pds_method_trans G (then_meth id_meth M) F L :- !,
	pds_method_trans G M F L.
pds_method_trans G (then_meth M1 M2) F (then_meth L (map_meth M2)) :-
	!, pds_method_trans G M1 F L.

pds_method_trans G (then_meths id_meth M2) F L :- !,
	pds_method_trans G M2 F L.
pds_method_trans G (then_meths M1 M2) F (then_meths L M2) :-
	!, pds_method_trans G M1 F L.

pds_method_trans G (orelse_meth M1 _M2) F L :-
	compound_goal G, !,
	pds_method_trans G M1 F L.

pds_method_trans G (orelse_meth M1 _M2) F L :-
	pds_method_trans G M1 F L.

pds_method_trans G (orelse_meth _M1 M2) F L :- !,
	pds_method_trans G M2 F L.

pds_method_trans G (try_meth M) F L :- !,
	pds_method_trans G (orelse_meth M id_meth) F L.

pds_method_trans G (cond_meth C M1 M2) F L :-
	(C G), !,
	pds_method_trans G M1 F L.

pds_method_trans G (cond_meth C M1 M2) F L :-
	(not (C G)), !,
	pds_method_trans G M2 F L.

pds_method_trans G (complete_meth M) F L :-
	!, pds_method_trans G (then_meth M triv_meth) F L.

pds_method_trans G (map_meth M) F L:-
	!, pds_method_trans G M F L.

pds_method_trans G (best_meth MethList) Best id_meth:-
	!, select_best_method G MethList Best.

pds_method_trans _ M M id_meth:-
	(not (M = (cut_meth _))),
	!.


%%%% Best-first selection mechanism
/* Selects the `best' method for the current goal, by evaluating the heuristic
 scores for each method and returning the method with the lowest score
(then the next lowest, and so on) */

kind meth_score type.

local method_score meth -> int -> meth_score.
local score_methods goal -> (list meth) -> (list meth_score) -> o.
local insert_methscore meth_score -> (list meth_score) -> (list meth_score) -> o.
local get_best_meth (list meth_score) -> meth_score -> o.
local pprint_methodscorelist (list meth_score) -> o.
local select_best_method goal -> (list meth) -> meth -> o.

select_best_method Goal MethodList BestMethod:- 
	score_methods Goal MethodList MethodScoreList, !,
	%% pprint_methodscorelist MethodScoreList, !,
	get_best_meth MethodScoreList (method_score M S),
	print "Selected method: ", pprint_name M,
	print "Heuristic score: ", pprint_name S,
	BestMethod = M.


%% Score each method and build the score list in ascending order.
%% The scoring predicate score_method for each method must be written in the
%% same module as the method definition (or higher).

score_methods Goal nil nil.	
score_methods Goal (M::Rest) MethodScoreList:-
	%% print "Scoring method: ", pprint_name M,
	score_method Goal M S,
	score_methods Goal Rest RestScoreList,
	insert_methscore (method_score M S) RestScoreList MethodScoreList.

insert_methscore MScore nil [MScore].
insert_methscore MScore RestScoreList MethodScoreList:-
	MScore = (method_score Meth Score),
	RestScoreList = ((method_score NextM NextS)::Rest),
	Score < NextS, 
	MethodScoreList = (MScore::RestScoreList).
insert_methscore MScore RestScoreList MethodScoreList:-
	RestScoreList = (First::Rest),
	insert_methscore MScore Rest ScoreList,  
	MethodScoreList = (First::ScoreList).

%% Select a method from the (ordered) score list, best first

get_best_meth (H::T) BestM:-
	BestM = H; get_best_meth T BestM. 

%% prints method score list (for diagnostic purposes)

pprint_methodscorelist ((method_score M S)::Rest):-
	pprint_name M, pprint_name S, pprint_methodscorelist Rest.
pprint_methodscorelist nil.



/* JB: build_plan is called by context_planner when it reaches an
empty agenda.  It uses the context plan information (which is asserted
using => as the plan is generated) to retrieve the plan nodes one by
one and create the associated "cplan", which is a cut-down version of
the actual plan.  The "cplan" is the one that gets printed at the end
of the planning attempt if plan printing is switched on. */

%%%%%%  E.M 5th Feb. Commented out quite a lot to do with the interactive mode
%%%%%%%   Claudio wanted plan printing, and it was failing as it was.


%build_plan _ eplan:- 
%	interactive_mode command.
build_plan Address (c_and_node G Address M Children):-
	retrieve_node Address K,
	(K = (and_node G Address C M Pre T)),
	build_child_nodes 1 Address Children,
	%read _,
        !.
build_plan Address (c_forall_node Address AtoPlan):-
	retrieve_node Address K,
%%	printstdout K,
	(K = (forall_node Address Type _)),
	retrieve_binder Address Binder,
	build_plan (1::Address) (AtoPlan Binder), 
	%read _,
	!.
build_plan Address (c_exists_node Address AtoPlan):-
	retrieve_node Address K,
%%	printstdout K,
	(K = (exists_node Address Type _)),
	retrieve_binder Address Binder,
	build_plan (1::Address) (AtoPlan Binder), 
	!.
build_plan Address eplan:-
	retrieve_node Address K, 
%%	printstdout K,
	%% Need to separated this because we're interested in the _first_
	%% success.  We maybe should do this elsewhere too - not sure.
	(K = emptyPlan),
	%read _,
	!.

build_child_nodes N Address nil:-
        retrieve_node (N::Address) K, 
        (K = emptyPlan),
	%read _,
        !.
build_child_nodes N Address (H::T):-
        build_plan (N::Address) H, !,
        N1 is (N + 1),
        build_child_nodes N1 Address T, 
	%read _,
        !.


end
