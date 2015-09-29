/* 

File: induction.mod
Author: Louise Dennis / James Brotherston
Description: Induction Methods
Last Modified: 20th August 2002

*/

module induction.

accumulate schemes, generalise, pwf.

local   sink_match      osyn -> osyn -> o.

local apply_suggestion (list subst) -> int -> int -> scheme -> goal -> scheme -> goal -> o.
local   merge_scheme scheme -> scheme -> scheme -> o.
local count_quantifiers osyn -> int -> o.

lemma induction triv_abs equiv
	trueP
	(app (abs X\ X) W)
	W.

compound induction trivials
	(complete_meth (repeat_meth (orelse_meth (orelse_meth all_i trivial) equality_condition)))
	_
	true.

atomic induction equality_condition
	(seqGoal (H >>> (app eq (tuple [A, B]))))
	(rewrite_with_rules [idty, triv_abs] Rule (app eq (tuple [A, B])) G1 Cond,		 
	trivial_condition Cond H)
	true
	(seqGoal ( H >>> G1))
	notacticyet.

atomic induction truegoalmeth
	(ripGoal (H >>> trueP) Skel E)
	true
	true
	(ripGoal (H >>> trueP) Skel E)
	notacticyet.
atomic induction truegoalmeth
	(seqGoal (H >>> trueP))
	true
	true
	(seqGoal (H >>> trueP))
	notacticyet.
atomic induction fertilisation_strong
	( ripGoal (H >>> G) Skel E )
	(memb (hyp H1 _) H,
	 sink_match_ H1 G Gout)  %jndw 2/12: modulo matching of sinks
	true 
	(ripGoal (H >>> Gout) Skel E)
	notacticyet.

atomic induction fertilisation_strong
	( seqGoal (H >>> G))
	( memb (hyp H1 _) H,
	 sink_match_ H1 G Gout)  %jndw 2/12: modulo matching of sinks
	true 
	(seqGoal (H >>> Gout))
	notacticyet.
	

%
% Weak fertilisation. Attempts to use a hypothesis L=R as a rewrite
% rule left-to-right or right-to-left, deleting the used hypothesis
% from the hypothesis list. Alternatively, if a copy of the entire hypothesis
% appears in the goal, it is replaced by trueP, and the used hypothesis is
% retained.
%

% no case for sinks yet
atomic induction fertilisation_weak
        ( ripGoal (H >>> G ) Skel E )
        ( memb_and_rest (hyp Hyp ind_hyp) H NewHyps,
         (rewrite_using Hyp G G1 _;
       % where hypothesis is an =ty

           rewrite_using_prop Hyp G G1) % for more general propositions
					% e.g. filapp which reduces to
					% A /\ B where we want to 
					% "strong" fertilise B with hyp.
					)
        true 
	( ripGoal ( NewHyps >>> G1 ) Skel E)
        notacticyet.

atomic induction fertilisation_weak
        ( seqGoal (H >>> G ))
        ( memb_and_rest (hyp Hyp ind_hyp) H NewHyps,
         (rewrite_using Hyp G G1 _%;
       % where hypothesis is an =ty

           %rewrite_using_prop Hyp G G1
) % for more general propositions
					% e.g. filapp which reduces to
					% A /\ B where we want to 
					% "strong" fertilise B with hyp.
	)
        true 
	( seqGoal ( NewHyps >>> G1 ))
        notacticyet.


atomic induction (induction_meth _I Scheme Subst)
    (seqGoal (H >>> G)) 
%% Louise 11th Jan added H to all_ripple_analysis - attempt to induct on skolem
%% constants - think this is a hack.... maybe.

%% Count the number of quantifers (i.e. potential number of variables to be used to 
%% induct upon and produce a list of possible induction schemes.
    ( 	% pprint_string "Counting quantifiers",
	count_quantifiers G Max,
	%	printstdout Max,
	pprint_string "Ripple analysis",
	all_ripple_analysis Max H G Suggestion,
	pprint_string "Applying suggestion",
	printstdout Suggestion,
	apply_suggestion Suggestion 0 0 no_scheme (seqGoal (H >>> G)) Scheme Subgoals
	)
    true
    Subgoals  
    notacticyet.
change_method_vars (induction_meth _ _ _) (induction_meth _ _ _).
 

% suggestion may involve more than one variable.

apply_suggestion Suggestion N1 _ SchemeIn SGIn SchemeIn SGIn:-
	not (
	nth Suggestion N Subst _,
		not (Subst = empty), 
		N > N1).
apply_suggestion Suggestion N1 C SI G SO SGO:-
	nth Suggestion N Subst _,
	not (Subst = empty), 
	% what is happening here is I have a list of induciton schemes to be applied to 
	% each universally quantified variable.  These appear in the same order as the variables.
	% nth will pick (the meaningul (i.e. not empty ones of) these out in order, returning N 
        % which is the place in the list they appear.  N is then used to apply them to the correct
	% variable in the goal.  In order to force them all to be chosen I pass N as an argument
        % to the recursive case and require that the next one picked is further into the list
	% i.e. N > N1 below!
	N > N1, !,

	% My next problem is that once I've applied a scheme I have one less universal quantifier 
	% in the goal - so N is out of sync with the quantifiers.  So I've introduced C which
	% counts the number of times I've applied the scheme and take this away from N in 
	% order to continue to identify the correct quantifier.
	N2 is N - C,
	applicable_induction_scheme Scheme Subst G N2 Subgoals,
	merge_scheme SI Scheme Schemes,
	C1 is C + 1,
	
	% I pass Subgoals as the new goal and applicable_induction_scheme works sensibly on compound
	% goals.
	apply_suggestion Suggestion N C1 Schemes Subgoals SO SGO.

merge_scheme no_scheme Scheme Scheme:- !.
merge_scheme S1 S2 (and_scheme S1 S2).

count_quantifiers (app forall (tuple [Type, (abs x\ (F x))])) N:-
	!, pi x\ (count_quantifiers (F x) N1),
	N is N1 + 1.
count_quantifiers P 0.

%jndw 2/12
% doesn't yet check that the sinks are equalised '
% Louise: Does now (I think!)

sink_match X X :- !.
sink_match (app forall (tuple [Type, (abs X)])) (app forall (tuple [Type, (abs Y)])):- !,
    sink_match (X Z) (Y Z).
sink_match (app forall (tuple [Type, (abs X)])) Y:- !,
    sink_match (X Z) Y.
sink_match (app exists (tuple [Type, (abs X)])) Y:- !,
    sink_match (X N) Y.
sink_match (abs X) (abs Y):-
    pi z\ (sink_match (X z) (Y z)), !.
sink_match (app F A) (app F B):-
    sink_match A B.
sink_match (app F A) B:-
	headvar_osyn F,
    sink_match A B.
sink_match A (app G B):-
	headvar_osyn G,
	(not (headvar_osyn B)),
    sink_match A B.
sink_match (app F A) (app G A):-
    sink_match F G, !.
sink_match (tuple L) (tuple M):-
    mappred L sink_match M, !.

sink_match_ X Y trueP:- 
	sink_match X Y, 
	!.
sink_match_ A (app F B) (app F Out):-
    sink_match_ A B Out, !.
sink_match_ L (tuple M) (tuple Mout):-
	nth M N MIn MRest,
	sink_match_ L MIn Out,
	nth Mout N Out MRest.

compound induction (induction_top IndType) (complete_meth
		(repeat_meth
		(orelse_meth trivials
		(orelse_meth allFi
	 	(orelse_meth taut
            	(orelse_meth sym_eval
		(orelse_meth existential
		(orelse_meth (repeat_meth generalise)
                         (ind_strat IndType)
	))))))))
	_
	true.

compound induction (step_case normal_ind)
        ( cut_meth
	(then_meth
           ( then_meth (try_meth (repeat_meth all_i)) set_up_ripple)

	(then_meth 
	
	(orelse_meth
	(then_meth
	   (repeat_meth (wave_method outward R))
	      (orelse_meth (repeat_meth fertilisation_strong)
		(then_meth	
		   (try_meth (repeat_meth 
                      (wave_method inout R1)))
		   (try_meth fertilise)
		)
	      )
	)
	
	
	(then_meth	
	   (repeat_meth 
              (wave_method inout R1))
	   fertilise
	))
	

	(then_meth post_ripple (then_meth
		(then_meth (try_meth sym_eval) (try_meth fertilise))
		(try_meth (repeat_meth all_e))))
		
	)))
	_
	true.
                   

compound induction (step_case with_critics)
        ( cut_meth
	(then_meth
           ( then_meth (try_meth (repeat_meth all_i)) set_up_ripple)

	(then_meth 
	
	(orelse_meth
	(then_meth
	   (repeat_meth (wave_method outward R))
	      (orelse_meth (repeat_meth fertilisation_strong)
		(then_meth	
		   (try_meth (repeat_meth 
                      (then_meth (patch_meth (wave_method inout R1) wave_critic_strat) (try_meth fertilisation_strong))))
		   (try_meth fertilise)
		)
	      )
	)
	
	
	(then_meth	
	   (repeat_meth 
              (then_meth (patch_meth (wave_method inout R1) wave_critic_strat)
		(try_meth fertilisation_strong)))
	   fertilise
	))
	

	(then_meth post_ripple (then_meth
		(then_meth (try_meth sym_eval) (try_meth fertilise))
		(try_meth (repeat_meth all_e))))
		
	)))
	_
	true.
                   

compound induction fertilise
        ( cut_meth 
            (orelse_meth
            (repeat_meth (orelse_meth
	       fertilisation_strong		
	       (orelse_meth fertilisation_weak
	       piecewise_fertilisation)))
			truegoalmeth))
	_
	true.

/*
compound induction (ind_strat whisky_ind)
      ( then_meths (induction_meth with_critics Scheme Subst)
                   (pair_meth (map_meth id_meth) (map_meth (step_case with_critics))))
	_
	true.
*/

compound induction (ind_strat IndType)
      ( then_meths (induction_meth IndType Scheme Subst)
                   (pair_meth (map_meth (step_case IndType)) (map_meth id_meth)) )
	_
	true.


% Special case for inductoin
atomic constructive_logic all_e
        (seqGoal (H >>> G))
        (memb_and_rest (hyp (otype_of X T) _) H NewH, 
	 subterm_of G X _,
	 (not (memb (hyp K An) NewH, not(An = ind_hyp), subterm_of K X _)), 
	 ((memb (hyp K ind_hyp) NewH, subterm_of K X _, NewHyp = H);
	  not ((memb (hyp K ind_hyp) NewH, subterm_of K X _)), NewHyp = NewH),
         forall_elim X T G NewG,
         (not (subterm_of NewG X _)))
        true
        (seqGoal (NewH >>> NewG))
        notacticyet.
end
