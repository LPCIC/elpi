/*

File:  wave.mod
Author: Louise Dennis / James Brotherston
Description: Support for Rippling
Last Modified: 20th August 2002

*/

module wave.

accumulate casesplit.

local sinkable_flag etree -> int -> o.
local fun_abs (list osyn) -> (list osyn) -> o.
local wcongr_ripple (list osyn) -> (list etree) -> (list etree) -> (mkey -> rewrite_rule -> osyn -> osyn -> osyn -> polarity -> o) -> mkey -> rewrite_rule -> osyn -> osyn -> osyn -> polarity -> (list int) -> (list int) -> o.
local congr_ripple_skel (list osyn) -> (list etree) -> (list int) -> int -> (list osyn) -> (list etree) -> (list (list etree)) -> o.

local reform_emb int -> (list etree) -> (list etree) -> (list (list etree)) -> (list etree) -> o.

local failed_cond rewrite_rule -> ripFail.
% local failed_measure ripFail.

local  wave_failed  (list preconditions -> o -> ripFail -> o).
local forthose2 list A -> (A -> B -> C -> o) -> list B -> list C -> list A -> list D -> list D -> o.




%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Wave Methods
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%


atomic wave (wave_method Dir Rule)
	(ripGoal (Hyps >>> Goal) Skel E1)
	(ripple_rewrite MKey Rule Skel (Goal @@ E1) (NewGoal @@ E2) Cond TermPos,
	(trivial_condition Cond Hyps, 
	 (embeds_list E2 Skel NewGoal Skel2 E3 E1 E1p,
	 (measure_check MKey Dir E3 E1p TermPos Embedding Skel2 NewSkel, 
	 (for_each_cut Embedding sinkable)))))
	true
	(ripGoal (Hyps >>> NewGoal) NewSkel Embedding)
	notacticyet.
change_method_vars (wave_method Dir Rule) (wave_method Dir _) :- !.





% wave_casesplit_method intended to be invoked by a critic

atomic_critic wave (check_wave_case_split Rule)
	      Address
	      Agenda
	      (get_goal Address (ripGoal (Hyps >>> Conc) Skel E),
	      casesplit_analysis Hyps Conc Rule _ (X\ wave_rule_list X))
	      true
	      nil
	      Agenda.


atomic wave (wave_case_split Rule)
	(ripGoal (Hyps >>> Conc) Skel E)
	(casesplit_analysis Hyps Conc Rule Cases (X\ wave_rule_list X))
	(mapfun Cases (x\ (ripGoal (((hyp x nha)::Hyps) >>> Conc) Skel E)) GoalList,
		list2goal GoalList Outgoals)
	Outgoals
	notacticyet.
change_method_vars (wave_case_split Rule) (wave_case_split _):-!.

%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Wave Critics
%%
%%%%%%%%%%%%%%%%%%%%%%%%%

compound_critic wave wave_critic_strat
	(then_crit (pop_critic FailAd)
	(then_crit (subplan_crit FailAd (then_crit (wave_failure Failure Rule)
	 				 open_node))
		   (wave_patch Failure FailAd Rule))).

compound_critic wave (wave_patch (failed_cond Rule) Ad Rule)
	(subplan_crit Ad
		      (then_crit (check_wave_case_split Rule)
	(subplan_crit Ad 
	   (continue_crit (m\ (then_meth (wave_case_split Rule) 
		(map_meth m))))))).

/*
compound_critic wave (wave_patch (failed_embed Rule) Ad Rule)
	(subplan_crit Ad
		(continue_crit (m\ (then_meth (end_plan) m)))).

atomic wave end_plan
	Goal
	(pprint_string "skeleton fails to embed")
	true
	trueGoal
	notacticyet.
*/
	

atomic_critic wave (wave_failure Failure Rule)
	Address
	Agenda
	(get_preconditions Address Pre, 
	 failed_pre Pre Failed,
	 wave_failed Pre Failed Failure)
	true
	nil
	Agenda.

%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Support Predicates
%%
%%%%%%%%%%%%%%%%%%%%%%%


%%%%%
% ripple_rewrite, just 1 step, not assuming that we really have an embedding
% - placing a variable where embedding will change

%version for merging congruency and embeddings 
%  Before is the Goal
%%%%
%% Louise:  Don't really understand what this predicate does at all.

%% MKey is used to indicate whether or not a reduction rule has been 
%% employed.  The importance of this is that "simplification within wave front"
%% as mentioned by Andrew Ireland's critics paper wrt. generalisation critic
%% must require non measure reducing reduction steps - i.e the measure
%% can be <= if a reduction rule has been used since the reduction order
%% combines with the measure and still guarantees termination (*ahem* -
%% asuming you actual have a sensible order on your reduction rules)
%% I'm not aware of _any_ literature about this which concerns me - Louise.

%% Nope that didn't work!!  I think this is more complex and maybe
%% relates to "unblocking" literature.
/*
ripple_rewrite MKey Rule Skel (Before @@ E1) (After @@ E2) Cond TermPos:-
     wave_rules_list RL,
	wcongr_ripple Skel E1 E2 
                (MK\ R\ X\ Y\ C\ P\ (sigma Emb\ (memb R RL,
			(not (bad_for_synthesis R X)),
			((rewr R P X Y C, MK = red);  
			 (rewr R P Y X C, MK = nored)),
			(not (embeds Emb X Y)))))
                                    MKey Rule Before After Cond P nil TermPos.
*/

%% JB: Ewen M's version of ripple_rewrite, which takes account of directions

ripple_rewrite MKey Rule Skel (Before @@ E1) (After @@ E2) Cond TermPos:-
     wave_rules_list RL,
        wcongr_ripple Skel E1 E2 
                (MK\ R\ X\ Y\ C\ P\ (sigma Emb\ (memb R RL,
                        ((rewr R positive_polarity X Y C, MK = red);
                         (rewr R negative_polarity Y X C, MK = nored)),
                        (not (bad_for_synthesis R Y)),
                        (not (embeds Emb X Y)))))
                                    MKey Rule Before After Cond P nil TermPos.


/*
wcongr_ripple Skel OldE NewE Rewr MK R Before Afters Cond P Pos NPos:-
	      printstdout Before,
	      fail.
*/

%% Check Term is not a metavariable.
wcongr_ripple Skel OldE NewE _Rewr _MK _R X _Y _C _P _TermPos _:-
 	headvar_osyn X,
     !,fail.

wcongr_ripple Skel OldE NewE Rewr MK R (polar_term XPolarity X) Y Cond Polarity TermPos TOut:-
	(not (headvar_osyn X)),
  multiply_polarities Polarity XPolarity NewPolarity,
  wcongr_ripple Skel OldE NewE Rewr MK R X Y Cond NewPolarity TermPos TOut.
  

%rewrite applies -- find new embedding
wcongr_ripple Skel OldE NewE Rewr MK R X Y Cond Polarity TermPos TermPos:-
    Rewr MK R X Y Cond Polarity.

/*
wcongr_ripple Skel OldE NewE Rewr MK R (abs In) (abs Out) Cond P TermPos TOut:-
     pi x \ ( fun_abs Skel S, 
        wcongr_ripple S OldE NewE Rewr MK R (In x) (Out x) Cond P TermPos TOut).
*/

wcongr_ripple Skel OldE NewE Rewr MK R (abs In) (abs Out) (abs Cond) P TermPos TOut:-
     pi x \ ( fun_abs Skel S, 
        wcongr_ripple S OldE NewE Rewr MK R (In x) (Out x) (Cond x) P TermPos TOut).

wcongr_ripple Skel OldE NewE Rewr MK R (app F A) (app F NewA) Cond P TermPos Tout:-
    polarise F A PolarA,
    congr_ripple_skel Skel OldE TermPos 2 NewSkel NewOldE RestE,
    wcongr_ripple NewSkel NewOldE NNewE Rewr MK R PolarA NewA Cond P (2 :: TermPos) Tout,
    reform_emb 2 OldE NNewE RestE NewE.

wcongr_ripple Skel OldE NewE Rewr MK R (app F A) (app NF A) Cond P TermPos Tout:-
    congr_ripple_skel Skel OldE TermPos 1 NewSkel NewOldE RestE,
    wcongr_ripple NewSkel NewOldE NNewE Rewr MK R F NF Cond P (1 :: TermPos) Tout,
    reform_emb 1 OldE NNewE RestE NewE.

wcongr_ripple Skel OldE NewE Rewr MK R (tuple L) (tuple NewL)
Cond P TermPos Tout:-
    congr_ripple_skel Skel OldE TermPos N NewSkel NewOldE RestE,
    nth L N A Rest,
    wcongr_ripple NewSkel NewOldE NNewE Rewr MK R A NewA Cond P (N :: TermPos) Tout,
	mappred Rest unpolarise UnPolarRest,
    nth NewL N NewA UnPolarRest,
    reform_emb N OldE NNewE RestE NewE.


%%% Sinkability
%% sinkable +Etree
%% sinkable_flag Etree -Flag
%
% Checks an embedding for sinks below all inwards wave-fronts.
% Flag set to 1 if sink present, 0 otherwise.

sinkable E:-
	(not (not (E = (leaf _ _)))),
	(not (not (E = (node _ _ _ _)))), !, fail.
sinkable E:- 
	sinkable_flag E X, (not (X = 2)).

% Direction at non-sink leaf must be outward
sinkable_flag (leaf outward _) 0.
sinkable_flag (leaf inward _) 2.

% At sink leaf set flag to 1.
sinkable_flag (sink _ _) 1.

% Inwards wave front
sinkable_flag (node inward _ F E) 1:-
	% Check subterm
	((sinkable_flag E 1);
	(sinkable_flag F 1)).

% Outward wave front
sinkable_flag (node outward _ F E) X:-
	((sinkable_flag E X, sinkable F);
	(sinkable_flag F X, sinkable E)),
	(not (X = 2)).

%node2 direction is ignored (assumed to be same surrounding noe)
sinkable_flag (node2 outward _ Elist) X:-
	% Check Subterms
	for_one Elist (Y\ (sinkable_flag Y X)) _, !,
	(not (X = 2)),
	for_each_cut Elist sinkable.

sinkable_flag (node2 inward _ Elist) X:-
	% Check Subterms
	for_one Elist (Y\ (sinkable_flag Y 1)) _, !.

%%%
%
% Wave Failed
% 
%%%

wave_failed _ (ripple_rewrite _ _ _ _ _ _ _) failed_rewrite.
wave_failed Pre (trivial_condition _ _) (failed_cond Rule):-
	success_pre Pre (ripple_rewrite _ Rule _ _ _ _ _),
	success_pre Pre (embeds_list _ _ _ _ _ _ _).
wave_failed Pre (embeds_list _ _ _ _ _ _ _) (failed_embed Rule):-
	success_pre Pre (trivial_condition _ _),
	success_pre Pre (ripple_rewrite _ Rule _ _ _ _ _).
/* wave_failed Pre (measure_check _ _ _ _ _ _ _ _) (failed_embed Rule):-
	success_pre Pre (trivial_condition _ _),
	success_pre Pre (ripple_rewrite _ Rule _ _ _ _ _). */
wave_failed _ (measure_check _ _ _ _ _ _ _ _) failed_measure.
wave_failed Pre (for_each_cut EList sinkable) (failed_sink E NewGoal):-
	success_pre Pre (ripple_rewrite _ _ _ _ (NewGoal @@ _) _ _),
	printstdout NewGoal,
	memb E EList.

%%%%%


atomic wave set_up_ripple
         ( seqGoal (H >>> Goal) )
         ( induction_hypothesis H Hl, 
	  ((congr (R\ P\ LHS\ RHS\ C\ 
               (rewr R P LHS RHS C)) beta_reduction positive_polarity Goal Goal2 _,
	   Hl = [(hyp Hl3 ind_hyp)],
	   congr (R\ P\ LHS\ RHS\ C\ 
               (rewr R P LHS RHS C)) beta_reduction positive_polarity Hl3 Hl4 _,
	  nth H N (hyp Hl3 ind_hyp) Rest,
	  nth H2 N (hyp Hl4 ind_hyp) Rest,
	   Hl2 = [(hyp Hl4 ind_hyp)]);
		(Goal = Goal2,
		Hl = Hl2, H2 = H)),
	  forthose E (Emb\ Hin\ Skel\ (strip_forall_embeds Hin Emb Skel Goal2)) Hl2 Hwork,
	  (not (Hwork = nil)), !
          )
          true
         (ripGoal (H2 >>> Goal2) Hwork E )
          notacticyet.



atomic wave post_ripple
         ( ripGoal Seq _F _E )
          true 
          true 
         (seqGoal Seq) 
         notacticyet.

atomic wave post_ripple
         (seqGoal Seq)
          true 
          true 
         (seqGoal Seq) 
         notacticyet.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% RIPPLING
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


wave_rules_list L :-
        wave_rule_list L, !.

wave_rule_list nil.

/*************************************************************************/
% Support Predicates for Rippling
/*************************************************************************/

%% embeds_list
%% Wrapper for embeds applied to lists.
embeds_list A B C Bwork A2 E1 E1p:- 
	copy_term C C1,
	forthose2 A (Emb\ Skel\ Bw\ (sigma S1\
                       (copy_term Skel S1,
			embeds Emb S1 C1, 
                        Bw = Skel))) B Bwork A2 E1 E1p, 
	(not (Bwork = nil)), !.


strip_forall_embeds (hyp (app forall (tuple [Type, (abs Prop)])) _) Emb Skel Conc:-
	strip_forall_embeds (hyp (Prop wild_card) _) Emb Skel Conc.
strip_forall_embeds (hyp (app exists (tuple [Type, (abs Prop)])) _) Emb Skel Conc:-
	strip_forall_embeds (hyp (Prop wild_card) _) Emb Skel Conc.
strip_forall_embeds (hyp Skel _) Emb Skel Conc:-
	embeds Emb Skel Conc.

%%  Recurse through list of skeletons and embeddings to find
%%  appropriate one(s) 
%%  for modification.  
%%  Save the "rest" of the embedding for remerging later.
congr_ripple_skel nil nil _ _ nil nil nil.
congr_ripple_skel ((app F Arg)::Skel) ((node _Dir TermPos Ftree Etree)::OldE) TermPos 1 (Arg::NewSkel) (Ftree::NewOldE) ([Etree]::RestE):-
    !,
    congr_ripple_skel Skel OldE TermPos 1 NewSkel NewOldE RestE.
congr_ripple_skel ((app F Arg)::Skel) ((node _Dir TermPos Ftree Etree)::OldE) TermPos 2 (Arg::NewSkel) (Etree::NewOldE) ([Ftree]::RestE):-
    !,
    congr_ripple_skel Skel OldE TermPos 2 NewSkel NewOldE RestE.
congr_ripple_skel ((tuple L)::Skel) ((node2 _Dir TermPos EtreeL)::OldE) TermPos N (A::NewSkel) (Etree1::NewOldE) (RestEtree::RestE):-
    !,
    nth L N A _Rest,
    nth EtreeL N Etree1 RestEtree,
    congr_ripple_skel Skel OldE TermPos N NewSkel NewOldE RestE.
%% Embedding and skeleton don't match - this embedding isn't an option.
congr_ripple_skel (S::Skel) (E::OldE) TermPos Pos (S::NewSkel) (E::NewOldE) ((dummytree::nil)::RestE):-
    congr_ripple_skel Skel OldE TermPos Pos NewSkel NewOldE RestE.

%%
% reform_emb
%%
%% Used to rebuilt the complete embedding by merging those bits that
%% have been changed with those bits that haven't

reform_emb _ nil nil _ nil.
%% We've lost this embedding.
reform_emb Pos (_O::OldE) (NN::NNewE) ((dummytree::nil)::RestE) (NN::NewE):-
    !,
    reform_emb Pos OldE NNewE RestE NewE.
reform_emb 1 ((node Dir Ad _ _)::OldE) (NN::NNewE) ([R]::RestE) ((node Dir Ad NN R)::NewE):-
    reform_emb 1 OldE NNewE RestE NewE.
reform_emb 2 ((node Dir Ad _ _)::OldE) (NN::NNewE) ([R]::RestE) ((node Dir Ad R NN)::NewE):-
    reform_emb 2 OldE NNewE RestE NewE.
reform_emb N ((node2 Dir Ad _EtreeL)::OldE) (NN::NNewE)
	     (Resttree::RestE) ((node2 Dir Ad Etree)::NewE):-
    nth Etree N NN Resttree,
    reform_emb N OldE NNewE RestE NewE.

%% fun_abs
%%%  This is to cope with recursing through abstractions in skeletons.
%% My thinking 
%% runs something along the lines of:  
%% The abs constructor never appears at a wave front.  So if the top
%% term in the skeleton is an abstraction then the part of 
%% the full term we have reached must be in this skeleton.  Thereforen
%% we do want to substitute the meta-variable. 
%%
%% This won't work because of substitution restriction in lprolog.  Therefore
%% we'll substitute with a Prolog meta-variable and hope that unification will
%% instantiate it correctly.

fun_abs nil nil:-!.
fun_abs ((abs H)::T) ((H _Var)::T1):- !,
    fun_abs T T1.
fun_abs (X::T) (X::T1):-
    fun_abs T T1.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	MEASURE CHECKING
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TermPos is the current position within the goal
% First arg is a key to see if we actually need to measure reduce
measure_check MKey Dir ENew EOld TermPos E3 Sin Sout:-  
    filter2 ENew EOld E3 Sin Sout (X\ Y\ Z\ (check_measure_reducing MKey Dir X Y TermPos Z)),
	(not (E3 = nil)), !.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  INDUCTION HYPOTHESIS
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    


%unsure what to do about this. At present, for multiple skels takes all
%hyps not of the form X $ Y. But could be other stuff (e.g. from casesplits)
%in there too. Need to fix.
induction_hypothesis ( (hyp H An) :: T ) ((hyp H An):: H1) :- 
		     (not (An = nha)),
		     !, induction_hypothesis T H1.
induction_hypothesis ( H :: T) T1 :- !, induction_hypothesis T T1.
induction_hypothesis nil nil :- !.


forthose2 nil P nil nil nil nil nil:- !.
forthose2 (X::L) P (Y::K) (W::Z) (X::Out) (A::AT) (A::BT):- P X Y W, !, forthose2 L P K Z Out AT BT.
forthose2 (X::L) P (Y::K) Z Out (_::AT) BT:- forthose2 L P K Z Out AT BT, !.

end


