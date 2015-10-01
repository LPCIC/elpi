/*

File: rewriting.mod
Author: Louise Dennis / James Brotherston
Description: Methods for Symbolic Evaluation.
Last Modified: 20th August 2002

*/

module rewriting.

accumulate embed.

local rewrite_ub osyn -> osyn -> osyn -> mkey -> polarity -> o.
local rewrite_ub_prop osyn -> osyn -> osyn -> o.
local tidy_lemma osyn -> osyn -> o.
% local tidy_lemma2 osyn -> osyn -> o.
                                       % form congruence from rewrite reln


% Apply a rewrite rule, taking care that the direction of the implication
% is compatible with the polarity of the expression being rewritten.
%
% Can always rewrite with equivalence-preserving rewrite rules, even
% when the "polarity" is equiv_only.
%
% This code is crude and should be improved to allow more external control
% (especially from symbolic evaluation) over what kinds of rewrite rules
% are allowed. We should have an additional category for "dangerous"
% rewrite rules which introduce meta-variables.

% JB: note also that the atomic rewriting methods can only deal with trivial
% side conditions on rewrites - that is to say, either the condition "trueP"
% or a condition which is already present in the hypotheses.


%%%%%%%%%%%
% ATOMIC METHODS
%%%%%%%%%%%

atomic rewriting rewrite_with_hyp
        (seqGoal (H >>> G))
        (memb_and_rest (hyp Hyp _) H Rest,
	  (not ((Hyp = (app eq (tuple [A, B])),
		member (otype_of A _) Rest,
		member (otype_of B _) Rest))),
	   NewHyps = Rest, 
         rewrite_using Hyp G G1 red)
%% skipped rewrite_using_prop - it was doing strange things with true!!
       % where hypothesis is an =ty
        true 
	(seqGoal (NewHyps >>> G1))
        notacticyet.

atomic rewriting (rewrite_with ListPredicate Rule)
        ( seqGoal (H >>> G))
        (ListPredicate List,
         rewrite_with_rules List Rule G G1 Cond,
         trivial_condition Cond H)
                              % check the condition is in the hypotheses
        true
        (seqGoal (H >>> G1))
        notacticyet.

atomic rewriting (rewrite_case_split ListPredicate Rule)
        ( seqGoal (H >>> G))
	(ListPredicate List,
         rewrite_with_rules List Rule G G1 Cond,
         (not (trivial_condition Cond H)),
	 casesplit_analysis H G Rule Cases ListPredicate)
	(mapfun Cases (x\ (seqGoal (((hyp x nha)::H) >>> G))) GoalList,
		list2goal GoalList Outgoals)
	Outgoals
	notacticyet.
change_method_vars (rewrite_case_split L Rule) (rewrite_case_split L _):-!.


%% JB: specialised rewriting methods that deal only with lemmas / defns

atomic rewriting (deploy_lemma Lemma)
	(seqGoal (H >>> G))
	(lemma_rewrites_list List,
	 rewrite_with_rules List Lemma G G1 Cond,
	 trivial_condition Cond H)
	true
        (seqGoal (H >>> G1))
	notacticyet.

atomic rewriting (unfold_defn Defn)
	(seqGoal (H >>> G))
	(defn_rewrites_list List,
	 rewrite_with_rules List Defn G G1 Cond,
	 trivial_condition Cond H)
	true
        (seqGoal (H >>> G1))
	notacticyet.



%% This is to allow rules to be differently instantiated by each call
%% to rewrite_with, deploy_lemma and unfold_defn under a repeat_meth.
%%
%% It is assumed that the ListPredicate has been given.
change_method_vars (rewrite_with ListPredicate Rule) (rewrite_with ListPredicate _) :- !.
change_method_vars (deploy_lemma Lemma) (deploy_lemma _) :- !.
change_method_vars (unfold_defn Defn) (unfold_defn _) :- !.


%%%%%%%%%%%%
% COMPOUND METHODS
%%%%%%%%%%%%

compound rewriting sym_eval
      (cut_meth
        (repeat_meth 
             ( orelse_meth 
                 (orelse_meth 
			( rewrite_with sym_eval_rewrites_list (R:rewrite_rule))
/*			(orelse_meth 
				(rewrite_case_split sym_eval_rewrites_list (R1:rewrite_rule))	*/
				rewrite_with_hyp)
/* ) */
                redundant
             )
        
	 )
       )
      Address
	true.

compound rewriting general_rewriting
        (repeat_meth 
             ( orelse_meth 
              ( rewrite_with general_rewrites_list R)
                redundant
             )
        
	 )
      Address
      ((Address=[];
	(Address=(H::T), 
         get_method T Meth, 
         (not (Meth = (rewrite_with _ _)))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Code for Preconditions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% rewriting with specified rules
%
% Try equivalences first.

rewrite_with_rules RL X Left Right Cond :-
        congr (R\ P\ LHS\ RHS\ C\ 
               (memb R RL, 
               rewr R P LHS RHS C)) X positive_polarity Left Right Cond.

% congr takes formula rewrites and closes over formulas

%  Note that this version will not instantiate a meta-var on its own
%  to lhs of rewrite.  

congr Rewr R P X Y Cond :- 
	(not (headvar_osyn X)),
        Rewr R P X Y Cond,
	(not (bad_for_synthesis R Y)),
	(not (X = Y)).

% function type

/*
congr Rewr R P (abs In) (abs Out) Cond:-
        pi ( x\ (
		(not ((In x) = x)),
		(congr Rewr R P (In x) (Out x) Cond)
	)), !.
*/

congr Rewr R P (abs In) (abs Out) (abs Cond):-
        pi ( x\ (
		(not ((In x) = x)),
		(congr Rewr R P (In x) (Out x) (Cond x))
	)).

% application terms
%
% Rewrite one argument.
%
%
% Must tag each function argument with a polarity, e.g. imp/2 lends
% polarity -,+ to its arguments. The polarity of a subexpression of a
% term T is calculated by multiplying its polarities relative to all the
% subexpressions of T. But how about polarity of a (maybe ground)
% subterm s_k of a term with flexible head, (H s_1 ... s_n) (which is
% itself a subterm of an expression E)? It seems we need to either build
% a constraint which relates the polarity of s_k to the (currently
% unknown) polar character of H, i.e.  p(s_k, E) = p(H, E) * q(H,K),
% where q(F,k) specifies the polarity of the kth argument of F.
% What about curried functions? We could just forget about it and 
% check in the object-level proof. Hmmm... interesting.
%

% Polarity is explained in Santiago's thesis.  In general the idea
% is that you do forward reasoning in the hypotheses - negative polarity
% and backwards reasoning in the goal - positive polarity.  Implication
% and negations (~ X is treated as X => false) complicate this since the
% LHS of an implication can be moved into the hypotheses.  Not sure
% whether a special case is needed for rewriting function symbols - I've
% assumed not that they just carry the polarity of the surrounding context.


congr Rewr R Polarity (app F In) (app F Out) Cond :-
	(not (headvar_osyn In)),
  polarise F In PolarIn,
  congr Rewr R Polarity PolarIn Out Cond.

congr Rewr R Polarity (app FIn Arg) (app FOut Arg) Cond :-
	(not (headvar_osyn FIn)),
  congr Rewr R Polarity FIn FOut Cond.

congr Rewr R Polarity (tuple L) (tuple OutL) Cond:-
  nth L N A Rest,
	(not (headvar_osyn A)),
  congr Rewr R Polarity A OutA Cond,
  mappred Rest unpolarise OutRest,
  nth OutL N OutA OutRest.

congr Rewr R Polarity (polar_term XPolarity X) Xout Cond:-
	(not (headvar_osyn X)),
  multiply_polarities Polarity XPolarity NewPolarity,
  congr Rewr R NewPolarity X Xout Cond.


%%  Splitting into two cases to handle problems caused by
%%  unification when a user enters rewrite rule.  The fix
%%  slows things down a lot and so is applied only to user rewrites.

rewr (user_rewrite RuleName) _Polarity LHS RHS Cond :-
     definition _ (user_rewrite  RuleName) CondA LHSA RHSA,
	/*  This terribly convoluted way of doing instantiation is to prevent 
	problems with instantiation of rewrite rules users have introduced at
	the command line */
	copy_term (tuple [CondA, LHSA, RHSA]) (tuple [Cond, LHS, RHS]).

rewr RuleName _P LHS RHS C:-
	definition _ RuleName C LHS RHS.


rewr (user_rewrite RuleName) _Polarity LHS RHS Cond :-
     lemma _ (user_rewrite RuleName) equiv CondA LHSA RHSA,
	copy_term (tuple [CondA, LHSA, RHSA]) (tuple [Cond, LHS, RHS]).
rewr RuleName _Polarity LHS RHS Cond :-
     lemma _ RuleName equiv Cond LHS RHS.

rewr (user_rewrite RuleName) positive_polarity LHS RHS Cond :-
     lemma _ (user_rewrite RuleName) rtol CondA LHSA RHSA,
	copy_term (tuple [CondA, LHSA, RHSA]) (tuple [Cond, LHS, RHS]).
rewr RuleName positive_polarity LHS RHS Cond :-
     lemma _ RuleName rtol Cond LHS RHS.

rewr (user_rewrite RuleName) negative_polarity LHS RHS Cond :-
     lemma _ (user_rewrite RuleName) ltor CondA LHSA RHSA,  
	copy_term (tuple [CondA, LHSA, RHSA]) (tuple [Cond, LHS, RHS]).
rewr RuleName negative_polarity LHS RHS Cond :-
     lemma _ RuleName ltor Cond LHS RHS.

rewr (user_rewrite RuleName) _Polarity LHS RHS Cond :-
     axiom _ (user_rewrite RuleName) equiv CondA LHSA RHSA,
	copy_term (tuple [CondA, LHSA, RHSA]) (tuple [Cond, LHS, RHS]).
rewr RuleName _Polarity LHS RHS Cond :-
     axiom _ RuleName equiv Cond LHS RHS.

rewr (user_rewrite RuleName) positive_polarity LHS RHS Cond :-
     axiom _ (user_rewrite RuleName) rtol CondA LHSA RHSA,
	copy_term (tuple [CondA, LHSA, RHSA]) (tuple [Cond, LHS, RHS]).
rewr RuleName positive_polarity LHS RHS Cond :-
     axiom _ RuleName rtol Cond LHS RHS.

rewr (user_rewrite RuleName) negative_polarity LHS RHS Cond :-
     axiom _ (user_rewrite RuleName) ltor CondA LHSA RHSA,  
	copy_term (tuple [CondA, LHSA, RHSA]) (tuple [Cond, LHS, RHS]).
rewr RuleName negative_polarity LHS RHS Cond :-
     axiom _ RuleName ltor Cond LHS RHS.

polarise F X X:-
	headvar_osyn F, !.

polarise imp (tuple [L, R])
          (tuple [(polar_term negative_polarity L),
                  (polar_term positive_polarity R)]) :- !.

polarise iff (tuple [L, R])
         (tuple [(polar_term equiv_only L),
                 (polar_term equiv_only R)]) :- !.

polarise neg X (polar_term negative_polarity X) :- !.

polarise _ (tuple [A, B]) (tuple [A, B]) :- !.

polarise _ X X.

unpolarise (polar_term _ X) X :- !.
unpolarise X X.

% Take a list of fun_type_poly terms and wrap them using the polar_term/2 
% functor together with their polarities, depending on the function.
% If function has an unusual polarity, use that, otherwise mark all
% arguments as +ve.

% Multiply polarities.

multiply_polarities equiv_only _ equiv_only.

multiply_polarities positive_polarity positive_polarity positive_polarity.

multiply_polarities positive_polarity negative_polarity negative_polarity.

multiply_polarities negative_polarity positive_polarity negative_polarity.

multiply_polarities negative_polarity negative_polarity positive_polarity.


%%%
%% Trivial Conditions
%%%

trivial_condition trueP _:- !.
/* trivial_condition (abs x\ trueP) _:- !. */
trivial_condition Cond H:-
	member (hyp Cond _) H, !.
/* trivial_condition (abs x\ (app eq (tuple [x, x]))) _ :- !. */
trivial_condition (app eq (tuple [X, X])) _ :- !.
trivial_condition (app eq (tuple [X, Y])) H:-
	member (hyp (app eq (tuple [Y, X])) _) H, !.
trivial_condition (app neq (tuple [X, Y])) H:-
	member (hyp (app neq (tuple [Y, X])) _) H, !.
trivial_condition (app (abs K) X) H:-
	member (hyp (K X) _) H, !.
trivial_condition (abs Cond) H:-
	pi x\ (trivial_condition (Cond x) H), !.


bad_for_synthesis beta_reduction Y:-
	headvar_osyn Y.
bad_for_synthesis beta_reduction (app X _):-
	headvar_osyn X.
bad_for_synthesis beta_idty Y:-
	headvar_osyn Y.

% use eq (with some universal quantification) to rewrite
%  ---- should check object typing here.

rewrite_ub (app eq (tuple [A, B])) A B red _.     % allow rewriting in
rewrite_ub (app eq (tuple [A, B])) B A nored _.   % either direction
rewrite_ub (app forall (tuple [_, (abs F)])) A B Dir Pol:- 
      rewrite_ub (F _T) A B Dir Pol.
rewrite_ub Hyp Out (app F (tuple [C, D])) MKey positive_polarity:-
        tidy_lemma Hyp (app F (tuple [L, R])),
        lemma _ _ _ trueP (app transitive F) trueP,
        ((C = L, Out = (app F (tuple [R, D])));
         (D = R, Out = (app F (tuple [C, L])))).
rewrite_ub Hyp Out (app F (tuple [C, D])) MKey negative_polarity:-
        tidy_lemma Hyp (app F (tuple [L, R])),
        lemma _ _ _ trueP (app transitive F) trueP,
        ((C = R, Out = (app F (tuple [L, D])));
         (D = L, Out = (app F (tuple [C, R])))).


% For weak fertilisation with propositional hypotheses.

rewrite_ub_prop Hyp Hyp trueP.
rewrite_ub_prop (app forall (tuple [_, (abs H)])) A B:-
	rewrite_ub_prop (H _T) A B.

% Could exploit polarity to our advantage here to allow rewriting with 
% IHs which are implications.

%% LD.  Modifying this to handle transitive predicates.  Notes here taken
%% from clam comments by Ian Green (I think).
%% For a function symbol - for which transitivity holds, we can
%% perform the following transformations on sequents:
%% 1. L~R |- X~S(R) into L~R |- X~S(L) if R occurs positive in S, or
%% 2. L~R |- S(L)~X into L~R |- S(R)~X if L occurs positive in S, or
%% 3. L~R |- X~S(L) into L~R |- X~S(R) if L occurs negative in S, or
%% 4. L~R |- S(R)~X into L~R |- S(L)~X if R occurs negative in S.

%% LD. I disagree with the above (though it may hold for implication)
%% - see below.  Basically I can't see how its true unless S is known
%% to be monotonic wrt. ~

%%
%% where the wave fronts must be: ``S({R})'' etc.
%% These can be reprased as:
%% 
%% 1. substitute R by L in rhs when R occurs positive, or
%% 2. substitute L by R in lhs when L occurs positive, or
%% 3. substitute L by R in rhs when L occurs negative, or
%% 4. substitute R by L in lhs when R occurs negative
%% 
%% If ~ is also symmetrical, we can drop the requirements on polarity.
%% The method below implements 1-2 in one method. It knows about
%% a set of function symbols which are transitive. It then always
%% does a fertilization replacing R by L, but it can assign L and
%% R to either lhs and rhs or vice versa, so we get the symmetry
%% we want.

%% I've modified this slightly (since I started worrying about
%% monotonic S etc. and we have polarity for -> and = handled
%% in our congr predicate ) so
%% 1.  L~R |- S(X~R) into L~R |- S(X~L) if R occurs +ve
%% 2.  L~R |- S(L~X) into  L~R |- S(R~X) if L occurs +ve
%% 3.  L~R |- S(X~L) into L~R |- S(X~R) if L occurs -ve
%% 4.  L~R |- S(R~X) into L~R |- S(L~X) if L occurs -ve


rewrite_using (app forall (tuple [_, (abs F)])) A B Mkey:- 
	!, rewrite_using (F _T) A B Mkey.
rewrite_using Hyp F G Mkey:-
	tidy_lemma Hyp H,	
	% instantating free vars as wild card for checking embedding.
	(not (not (
	% ... or not as case may be - breaks qrevcorrect.
	 % tidy_lemma2 H HE, 
	embeds _ H F))),
      congr (r\ pol\ rp\ c\ cond\ (
	rewrite_ub H c rp Mkey pol)) _Rule positive_polarity F G _.
%% Comment out unless using with number theory
/*
rewrite_using Hyp F G Mkey:-
	tidy_lemma Hyp H,	
	% instantating free vars as wild card for checking embedding.
      congr (r\ pol\ rp\ c\ cond\ (
	rewrite_ub H rp c Mkey pol)) _Rule positive_polarity F G _.
*/

rewrite_using_prop (app forall (tuple [_, (abs F)])) A B :- 
	!, rewrite_using_prop (F _T) A B.
rewrite_using_prop Hyp F G :-
      congr (r\ pol\ rp\ c\ cond\ (rewrite_ub_prop Hyp rp c )) _Rule _ F G _.

tidy_lemma X X:-
	headvar_osyn X, !.
tidy_lemma X X:-
	obj_atom X.
tidy_lemma wild_card wild_card.
tidy_lemma (app F A) B:-
	not (headvar_osyn F),
	F = (abs x\x),
	tidy_lemma A B.
tidy_lemma (app F A) (app G B):-
	tidy_lemma F G,
	tidy_lemma A B.
tidy_lemma (tuple L) (tuple M):-
	mappred L tidy_lemma M.
tidy_lemma (abs F) (abs G):-
	pi (x\ (tidy_lemma (F x) (G x))).

/*
tidy_lemma2 wild_card wild_card:- !.
tidy_lemma2 X X:-
	obj_atom X.
tidy_lemma2 (app F A) B:-
	not (headvar_osyn F),
	F = (abs x\x),
	tidy_lemma2 A B.
tidy_lemma2 (app F A) (app G B):-
	tidy_lemma2 F G,
	tidy_lemma2 A B.
tidy_lemma2 (tuple L) (tuple M):-
	mappred L tidy_lemma2 M.
tidy_lemma2 (abs F) (abs G):-
	pi (x\ (tidy_lemma2 (F x) (G x))).
*/

%% JB: function to convert a goal to a (directed) lemma

goal_to_lemma ReasonType Goal Theory (user_rewrite Name) Dir Cond Lhs Rhs:-
   top_goal Theory Goal Hyps Conc,
   print "Theory found: ", pprint_name Theory,
   term_to_string Goal GoalName, 
   term_to_string ReasonType DirName,
   Name is (GoalName ^ "_" ^ DirName),
   print "Lemma name:   ", pprint_string Name,
   ((ReasonType = bwd, Dir = rtol) ; (ReasonType = fwd, Dir = ltor)), !,
   print "Direction:    ", pprint_name Dir,
   convert_hyps_to_cond Hyps Cond, !,
   print "Conditions:   ", pprint_name Cond,
   convert_conc_to_rewrite Dir Conc Lhs Rhs, !,
   pprint_string "Lemma:",
   pprint_term Lhs, print " ==> ", pprint_term Rhs.
   

local convert_hyps_to_cond (list osyn) -> osyn -> o.

convert_hyps_to_cond [] trueP:- !.
convert_hyps_to_cond [Hyp] Hyp:- !.
convert_hyps_to_cond (Hyp::RestHyps) (app and (tuple [Hyp, RestCond])):-
  convert_hyps_to_cond RestHyps RestCond.


local convert_conc_to_rewrite direction -> osyn -> osyn -> osyn -> o.

convert_conc_to_rewrite rtol (app imp (tuple [A,B])) B A.
convert_conc_to_rewrite ltor (app imp (tuple [A,B])) A B.
convert_conc_to_rewrite rtol (app eq (tuple [A,B])) B A.
convert_conc_to_rewrite ltor (app eq (tuple [A,B])) A B.
convert_conc_to_rewrite rtol (app iff (tuple [A,B])) B A.
convert_conc_to_rewrite ltor (app iff (tuple [A,B])) A B.
convert_conc_to_rewrite Dir (app forall (tuple [_Type, (abs X\ (F X))])) L R:- 
   (sigma Z\ (convert_conc_to_rewrite Dir (F Z) L R)).
convert_conc_to_rewrite Dir (app exists (tuple [_Type, (abs X\ (F X))])) L R:-
   (sigma Z\ (convert_conc_to_rewrite Dir (F Z) L R)).
convert_conc_to_rewrite Dir Other Other trueP.


local apply_casesplit (list osyn) -> osyn -> rewrite_rule -> (list osyn) -> (list rewrite_rule -> o) -> o.

local complete_cases osyn -> (list osyn) -> o.


%% wave_casesplit_method intended to be invoked by a critic

casesplit_analysis Hyps Term Rule Cases ListPred:-
        findall (x\ apply_casesplit Hyps Term Rule x ListPred) CaseList,
        memb Cases CaseList.

apply_casesplit Hyps Term Rule Cases ListPred:-
		ListPred L,
        %% Rule is instantiated as we come in, but just in case
        %% Check rule actual rewrites term somewhere
        rewrite_with_rules L Rule Term _ Cond,
        complete_cases Cond Cases,
        for_each Cases (x\ (not (member (hyp x _) Hyps))).
                     

complete_cases (app (abs F) X) Out:-
	complete_cases (F X) Out.
complete_cases (app neg X) [(app neg X), X]:-!.
complete_cases (app neq (tuple [X, Y])) [(app neq (tuple [X, Y])), (app eq (tuple [X, Y]))]:-!.
complete_cases (app eq (tuple [X, Y])) [(app eq (tuple [X, Y])), (app neq (tuple [X, Y]))]:-!.
complete_cases X [X, (app neg X)].

end
