/*

File: schemes.mod
Author: Louise Dennis / James Brotherston
Description: Induction Schemes
Last Modified: 20th August 2002

*/

module schemes.

%% was pick_quantifer shortened in attempt to help hash table
local pick_quantifier         osyn -> (list osyn) -> int -> osyn -> o.

%% was subst_insert shortened in attempt to help hash table
local subst_insert
    (pairing (list subst) (pairing int (pairing int int)))
    -> (list (pairing (list subst) (pairing int (pairing int int)))) ->
       (list (pairing (list subst) (pairing int (pairing int int)))) -> o.

%% was sort_suggestions - shortened in attempt to help hash table.
local subst_sort
       (list (pairing (list subst) (pairing int (pairing int int)))) ->
       (list (pairing (list subst) (pairing int (pairing int int)))) -> o.

%% Louise 11th Jan - adding H to ripple analysis
%% was ripple_analysis - shortened in attempt to help hash table.

%% Louise 11th Jan - adding H to ripple analysis

local ripple_analysis          (list subst) -> osyn -> osyn -> (list osyn) ->
                               int -> int -> int -> o.

local number_flaws            etree -> osyn -> osyn -> 
                               int -> int -> o.

local number_flaws_           etree -> osyn -> osyn -> 
                               int -> int -> (list int) -> osyn -> 
                               osyn -> o.

local number_flaws_list           (list etree) -> (list osyn) -> (list osyn) -> 
                               int -> int -> int -> (list int) -> osyn -> 
                               osyn -> o.

local depth_scheme 	osyn ->  osyn -> int -> o.
local inc_max int -> int -> o.

local scheme_list (list subst) -> osyn -> (list osyn) -> int -> o.


induction_schemes_list L :-
	induction_schemes_list_ L, 
	!.
induction_schemes_list_ nil.


% Generate a list of induction suggestions for the current goal. Each call
% to ra gives us one induction suggestion, which is essentially the 
% substitution performed in the step case of the goal. This is not yet
% applied to the goal.
%
% Max is maximum no of variables to induce upon

%% Louise 11th Jan - adding H to ripple analysis


%
% Collecting ripple_analysis suggestions
%
% does a setof and orders them, picks one.
all_ripple_analysis 0 _ _ _:- !, fail.
all_ripple_analysis Max H Goal S1:-
%% Louise 11th Jan - adding H to ripple analysis
% JIHG - prevent trivial schemes
	% efficency consideration - look for unflawed simple schemes first.
%%	inc_max Max SubMax,
	findall (SL\ (sigma Flag\ (scheme_list SL Goal H Flag, 
		not (Flag = 0)))) SchemeList,
%%	Flag stops all empty schemes.
	forthose SchemeList 
	(SL\ SFU\ Dummy\ sigma S\ sigma F\ sigma U\ sigma Sum\ sigma D\
 	(ripple_analysis SL Goal Goal H F U D,
	 Sum is F + U,
         Sum > 0,
	 SFU = (SL @@ (F @@ (D @@ U))))) SC _,
	%% efficiency consideration, is there an unflawed suggestion
/*	(memb (_ @@ (0 @@ (_ @@ _))) SC; SubMax = Max), */
        subst_sort SC SortedSC,
        !,
        memb (S1 @@ (F1 @@ U1)) SortedSC.

inc_max _ 1.
inc_max Max N:-
	inc_max Max M,
	N is M + 1,
	(N < Max; N = Max).
	

subst_sort nil nil.
subst_sort ((S @@ (F @@ U))::Subst_Sort) Z :-
        subst_sort Subst_Sort  Y,
        subst_insert (S @@ (F @@ U)) Y Z.

subst_insert A nil (A::nil).
subst_insert (S1 @@ (F1 @@ (D1 @@ U1))) ((S2 @@ (F2 @@ (D2 @@ U2)))::Subst_Sort)
         ((S1 @@ (F1 @@ (D1 @@ U1)))::(S2 @@ (F2 @@ (D2 @@ U2)))::Subst_Sort):- 
        (F1 < F2;
	((F1 = F2, D1 < D2);
        (F1 = F2, D1 = D2, U1 < U2))),
        !.

subst_insert (S1 @@ (F1 @@ U1)) ((S2 @@ (F2 @@ U2))::Ss) ((S2 @@ (F2 @@ U2))::Z) :- 
        subst_insert (S1 @@ (F1 @@ U1)) Ss Z.


%
% ra - ripple analysis code
%
%% Starting case.  Picks a scheme.  S is instantiated to something (e.g.
%% (dom a\ (repl a (app s a))) - replace the quantified variable you've
%% picked for a with s(a).  It then recurses through this expression
%% instantiating the Hypotheses and goal so it can count flaws.
/*
ripple_analysis P Q empty
          (app forall (tuple [T, H])) (app forall (tuple [T, G])) Hyps
          ((S @@ (Antecedent @@ Consequent))::Ss) F U D:- 
        P < Q,                                  % too many?
	induction_schemes_list List,
	memb Name List,
        induction_scheme _ Name T S _ Antecedent Consequent,
        PP is P + 1,
     ripple_analysis PP Q S (app forall (tuple [T, H])) (app forall (tuple [T, G])) Hyps Ss F U D.
*/

%% replacing the current variable (top forall) with its step case
ripple_analysis ((repl S E)::SL) 
		(app forall (tuple [T, (abs H)])) 
                  (app forall (tuple [T, (abs G)])) Hyps F U D:-
	depth_scheme S E D2,
        ripple_analysis SL (H S) (G E) Hyps F U D1,
	D is (D1 + D2).


%% "recursing" through the dom - dom is really used later.
ripple_analysis ((dom S)::SL) (app forall (tuple [T, H])) 
                (app forall (tuple [T, G])) Hyps F U D:-
        (pi (v \ (ripple_analysis ((S v)::SL) (app forall (tuple [T, H])) 
                               (app forall (tuple [T, G])) Hyps F U D))).

%% picking a different quantifier for instantiation (other than the top
%% quantifier.
ripple_analysis (empty::SL) (app forall (tuple [T, (abs H)])) 
              (app forall (tuple [T, (abs G)] )) Hyps F U D:- 
       (pi (v \ (ripple_analysis SL (H v) (G v) Hyps F U D))).

%% Louise 11th Jan - new base case (not a base case!!) --- looking for Skolem constants  -- sort out in a minute

ripple_analysis SL H G Hyps F U D:-
	not (SL = nil),
        not (G = (app forall _)),
	memb_and_rest (hyp (otype_of Var T) _) Hyps Rest,
	(H = (H1 Var)),
	(G = (G1 Var)),
	(not (subterm_of (app forall (tuple [T, (abs x\ (G1 x))])) Var _)),
	ripple_analysis SL (app forall (tuple [T, (abs H1)])) (app forall (tuple [T, (abs G1)])) Rest F U D.
/*
ripple_analysis P Q ?? H G Hyps
          ((S @@ (Antecedent @@ Consequent))::Ss) F U D:- 
        P < Q,                                  % too many?
        not (G = (app forall _)),
	memb (hyp (otype_of Var T) _) Hyps,
	(H = (H1 Var)),
	(G = (G1 Var)),
	(not (subterm_of (app forall (tuple [T, (abs x\ (G1 x))])) Var _)),
	induction_schemes_list List,
	memb Name List,
        induction_scheme _ Name T S _ Antecedent Consequent,
        PP is P + 1,
     ripple_analysis PP Q S (app forall (tuple [T, (abs H1)])) (app forall (tuple [T, (abs G1)])) Hyps Ss F U D.
*/

%% On reaching the "base case" try to embed and count the flaws.
ripple_analysis nil H G Hyps F U 0:-
        not (G = (app forall _)),
        %% ONLY TRY ONE EMBEDDING
        embeds E H G,
	!,
	% pprint_string "Counting flaws",
        number_flaws E H G F U.
	% pprint_string "finished counting flaws".

depth_scheme S S 0.
depth_scheme S (tuple Y) D:-
	for_one Y (X\ sigma De\ (depth_scheme S X De)) N,
	depth_scheme S N D.
depth_scheme S (app _ Y) D:-
	depth_scheme S Y D1,
	D is D1 + 1.
depth_scheme S (app Y _) D:-
	depth_scheme S Y D1,
	D is D1 + 1.

% recurse top-down through H and G, keeping an eye on E.  If E
% indicates that the top symbol of G is a wave-front try to ripple
% this annotated term.  If it ripples, it is unflawed, else it is
% flawed.  H and G do not contain free variables.

number_flaws E H G F U :-
        number_flaws_ E H G F U nil _ _,
        !.
	     

% no annotations in H so there are no flaws/unflaws.  
number_flaws_ _ H H 0 0 _ _ _ :- 
	% pprint_string "Flaws clause 1",
	!.

% at a leaf in the skeleton, so there cannot be wave-fronts below
% address of skeleton and erasure are the same, so there cannot be an
% interveninpg wave-front
number_flaws_ (leaf _ Ad) _ _ 0 0 Ad _ _ :- 
	% pprint_string "Flaws clause 2",
        !.

number_flaws_ (sink _ Ad) _ _ 0 0 Ad _ _ :- 
	% pprint_string "Flaws clause 3",
	!.

% Mirror embedding code by descending through lambda abstractions in two
% ways. Firstly when both input terms are abstractions.
%
number_flaws_ E (abs LambdaF) (abs LambdaG) L M Ad Hs Gs :-
	% pprint_string "Flaws clause 4 (pi)",
	pi z\ (number_flaws_ E (LambdaF z) (LambdaG z) L M Ad Hs Gs).

% address of skeleton and erasure disagree, so there is a wave-front
% in the superterm of Ad.  In this case, attempt to one-step-ripple
% the superterm. If this is possible the wave-occurrence is unflawed,
% otherwise it is flawed.

number_flaws_ Term _FT FU 0 1 _ Hs Gs :-
	% pprint_string "Flaws clause 5 (copy_term, embeds, memb)",
	(Term = (leaf _ _) ; Term = (sink _ _)),
	copy_term Gs Gp, 
	copy_term Hs Hp,
	wave_rule_list L,
	memb Name L,
	%% attempt to control synthesis
        rewr Name _ Gp NewG _Cond,
	% checking the "intended variable is the one that's been rewritten
	not (subterm_of NewG FU _),
        embeds _NewE Hp NewG,
        !.

number_flaws_ (leaf _ _) _FT _FU 1 0 _ _Hs Gs :-
	% pprint_string "Flaws clause 6",
        !.

number_flaws_ (sink _ _) _FT _FU 1 0 _ _Hs Gs :-
	% pprint_string "Flaws clause 7",
        !.

% Secondly when the second is an abstraction.
%
number_flaws_ E F (abs LambdaG) L M Ad Hs Gs :-
	% pprint_string "Flaws clause 8 (pi)",
	pi z\ (number_flaws_ E F (LambdaG z) L M Ad Hs Gs).

% address of skeleton and erasure are the same, so there cannot be an
% intervening wave-front
number_flaws_ (node _Dir Ad Ftree Tree) (app F T) (app NF U) L M Ad _Hs _Gs :-
	% pprint_string "Flaws clause 9 (number_flaws_list)",
        !,
        number_flaws_list [Ftree, Tree] [F, T] [NF, U] L M 0 Ad (app F T) (app NF U).

number_flaws_ (node2 _Dir Ad TreeL) (tuple L1) (tuple L2) L M Ad Hs Gs :-
        % pprint_string "Flaws clause 10 (number_flaws_list)",
	!,
        number_flaws_list TreeL L1 L2 L M 0 Ad Hs Gs.

% address of skeleton and erasure disagree, so there is a wave-front
% in the superterm of Ad.  In this case, attempt to one-step-ripple
% the superterm. If this is possible the wave-occurrence is unflawed,
% otherwise it is flawed.

number_flaws_ (node _Dir _ _Ftree _Tree) _FT FU 0 1 _ Hs Gs :-
	% pprint_string "Flaws clause 13 (copy_term, memb, embeds)",
	wave_rule_list L,
	memb Name L,
	copy_term Gs Gp, 
	copy_term Hs Hp,
	(not ((Hs = (app F _)), headvar_osyn F)),
	%% attempt to control synthesis
        rewr Name _ Gp NewG _Cond,
	% checking the "intended variable is the one that's been rewritten
	not (subterm_of NewG FU _),
        embeds _NewE Hp NewG,
	!.

number_flaws_ (node _Dir _ _ _Tree) _FT _FU 1 0 _ _Hs Gs :-
	% pprint_string "Flaws clause 14",
        !.

number_flaws_ (node2 _Dir _ _Trees) _FT _FU 1 0 _ _Hs Gs :-
	% pprint_string "Flaws clause 15",
        !.


number_flaws_list nil nil nil 0 0 _N _Pos _Hs _Gs.
	%:- pprint_string "Flaws clause 16".
number_flaws_list (H::T) (H1::T1) (H2::T2) LO MO N Pos Hs Gs:-
	% pprint_string "Flaws clause 17",
	N1 is N + 1,
	number_flaws_ H H1 H2 L1 M1 (N1::Pos) Hs Gs,
	number_flaws_list T T1 T2 L2 M2 N1 Pos Hs Gs,
	LO is L1 + L2,
	MO is M1 + M2.


% These first two clauses deal with situations when two schemes are being 
% applied at once.
% If the goal is an allGoal then the scheme is applied on an arbitrary 
% variable but because
% I want to return a base and a step case its distributed over the output 
% (I think this is logically sound!!!)

applicable_induction_scheme Name Subst (allGoal T (x\ (G2 x))) N ((allGoal T (x\ (S1 x))) ** (allGoal T (x\ (B1 x)))) :-
	pi x\ (applicable_induction_scheme Name Subst (G2 x) N ((S1 x) ** (B1 x))).

% This clause applied when a goal already consisting of a step and base case 
% is passed in
% It assume that _anything_ involving a base case should be treated as a 
% base case and
% so fiddles with the bracketing.  NB.  This effectively hard wires into the 
% system the order in which base and step cases are treated.

applicable_induction_scheme Name Subst (Step ** Base) N (S2 ** ((B2 ** S1) ** B1)) :-
	applicable_induction_scheme Name Subst Base N (S1 ** B1),
	applicable_induction_scheme Name Subst Step N (S2 ** B2).
applicable_induction_scheme Name Subst (seqGoal (H >>> X)) N Y :-
    pick_quantifier X H N X1,            % rearranges quantifiers to 
                                       % put selected one at the front.
    induction_schemes_list List,
    induction_scheme _ Name Ty Subst _ (seqGoal (H >>> X1)) Y,
    member Name List,

% Now ensure that the universally quantified variable on which
% we are performing induction actually appears in the goal (otherwise
% it does not make sense to perform induction on it).

    not (X1 = (app forall (tuple [_, (abs x\ _Prop)]))).

% Pick one of the leading universal quantifiers and place it
% at the front of the goal, returning N, the number of the quantifier which
% is placed at the front. 

pick_quantifier (app forall K) _ 1 (app forall K).

%% Louise 11th Jan - adding H to ripple analysis
pick_quantifier G H
    1 
     (app forall (tuple [T, (abs x\ (G1 x))])) :-
        not (G = (app forall _)),
	memb (otype_of Var T) H,
	(G = (G1 Var)),
	(not (subterm_of (app forall (tuple [T, (abs x\ (G1 x))])) Var _)).

pick_quantifier (app forall (tuple [Type1, (abs Prop1)])) H
    N 
     (app forall (tuple [Type2,
        (abs x\ (app forall (tuple [Type1, (abs y\ ((Prop2 y) x))])))])) :-
        pi z\ (pick_quantifier (Prop1 z) H N1 (app forall (tuple [Type2,
                                          (abs y\ ((Prop2 z) y))]))),
        N is N1 + 1.

scheme_list (S::L) (app forall (tuple [T, (abs H)])) Hyps 1:-
	induction_schemes_list List,
	memb Name List,
        induction_scheme _ Name T S _ Antecedent Consequent,
        pi v\ (scheme_list L (H v) Hyps _).
scheme_list (empty::L) (app forall (tuple [_T, (abs H)])) Hyps Flag:-
	    (pi v\ (scheme_list L (H v) Hyps Flag)).
scheme_list L G Hyps Flag:-
        not (G = (app forall _)),
	memb_and_rest (hyp (otype_of Var T) _) Hyps Rest,
	(G = (G1 Var)),
	(not (subterm_of (app forall (tuple [T, (abs x\ (G1 x))])) Var _)),
	scheme_list L (app forall (tuple [T, (abs x\ (G1 x))])) Rest Flag.
scheme_list nil G _ 0:- 
        not (G = (app forall _)).

	    

end
