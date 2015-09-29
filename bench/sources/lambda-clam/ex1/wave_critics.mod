/*

File: wave_critics.mod
Author: Louise Dennis / James Brotherston
Description: Induction engine including Andrew Ireland's critics  '
Last Modified: 21st August 2002

*/

module wave_critics.

accumulate induction.

local member_quant goal -> goal -> o.
local is_quantifier_in osyn -> int -> int -> o.
local unsinkable_flag int -> etree -> (list int) -> (list int) -> o.
local quantify_lemma (list osyn) -> osyn -> osyn -> o.
local partial_wave_rule_match goal -> goal -> rewrite_rule -> o.
local place_meta_vars osyn -> etree -> osyn -> (list int) -> int -> o.
local revise_induction goal -> scheme -> subst -> rewrite_rule -> goal -> scheme -> o.
local repeat_ripple_in goal -> goal -> rewrite_rule -> o.
local reverse_directions etree -> etree -> o.
local find_nearest_meth meth -> (list int) -> (list int) -> o.
local find_previous_meth meth -> (list int) -> (list int) -> o.
local parent_address (list int) -> (list int) -> o.
local construct_generalisation goal -> etree -> osyn -> osyn -> o.
local construct_gen_terms osyn -> osyn -> osyn -> osyn -> (list int) -> osyn -> int -> o.
local gen_term osyn -> osyn -> osyn -> osyn -> o.
local iterate_wave_fronts  osyn -> osyn -> osyn -> osyn -> o.

%% Induction Revision Critic

%%% ---- Critic code

%% Needs to be failed measure because otherwise you can always
%% rewrite back in with a wave rule that should have rewritten 
%% outwards

/*
compound_critic wave (wave_patch (failed_measure) Ad _Rule)
        (subplan_crit Ad
        (then_crit 
                (induction_revision (induction_meth _I Scheme Subst) Node) 
	(subplan_crit Node
		(continue_crit 
	       (m\ (then_meth (then_meths (induction_meth with_critics Scheme Subst)
               (pair_meth (map_meth (step_case with_critics)) (map_meth id_meth)) ) (induction_top with_critics))))))).
*/

atomic_critic wave (induction_revision (induction_meth _ Scheme Subst) Node)
	Address
	Agenda
	(get_goal Address G,
	 partial_wave_rule_match G NG Rule)
	(find_nearest_meth (induction_meth _ Sc _) Address Node,
	 get_goal Node Goal,
	revise_induction NG Scheme Subst Rule Goal Sc)
	nil
	Agenda.


%%% ---- Support Predicates


partial_wave_rule_match (ripGoal (Hyps >>> Conc) Skel Emb) (ripGoal (Hyps >>> NewConc) NewSkel Es) Rule:-
        memb E Emb,
        place_meta_vars Conc E NewConc nil 0,
        induction_hypothesis Hyps H,
        embeds_list Es Skel NewConc NewSkel NewEs _ _,
%	This bit can succeed by enlarging instead of moving the wave front.
%	We want the wave front to move.
        ripple_rewrite _MK Rule NewSkel (NewConc @@ NewEs ) (Temp @@ NewE) _ TermPos,
	embeds_list NewE NewSkel Temp NewNewSkel NNE Es Esp,
        measure_check MKey Dir NNE Esp TermPos Embedding NewNewSkel Skelp.
%	This bit can succeed by enlarging instead of moving the wave front.
%	We want the wave front to move.
%	mappred Es wave_front_moved NewE.

%% We want to place meta variables around all wave holes
%% These occur when there is a gap in the skeleton.
%% Andrews paper suggests (though it does not explicitly say
%% that meta-variables should surround sinks and wave holes
%% I use a flag 0 or 1 to indicate whether or not the predicate is
%% traversing a wave front.
%% place_meta_vars A B _ C D:-
%%%%    printstdout A,
%%      printstdout B,
%%      printstdout C,
%%      printstdout D,
%%      fail.
place_meta_vars Term (leaf _ Pos) Term Pos 0.
place_meta_vars Term (leaf _ Pos) (app M Term) Pos 1.
place_meta_vars Term (sink _ Pos) (app M Term) Pos _.
place_meta_vars (app F X) (node _ Pos FEtree AEtree) Out Pos Flag:-
        !,
        ((Flag = 0, NFlag = 0); (Flag = 1, NFlag = 0)),
        place_meta_vars F FEtree NF (1 :: Pos) NFlag,
        place_meta_vars X AEtree NX (2 :: Pos) NFlag,
        ((Flag = 0, Out = (app NF NX)); (Flag = 1, Out = (app M (app NF NX)))).
place_meta_vars (app F X) Etree (app NF NX) TermPos Flag:-
        place_meta_vars F Etree NF (1 :: TermPos) 1,
        place_meta_vars X Etree NX (2 :: TermPos) 1.
place_meta_vars (tuple L) (node2 _ Pos EtreeL) (tuple NL) Pos Flag:-
        !, 
        mapcount EtreeL
          (Tree\ Term\ NewTerm\ N\ 
                (place_meta_vars Term Tree NewTerm (N :: Pos) Flag)) L NL 1.
place_meta_vars (tuple L) Etree (tuple NL) TermPos Flag:-
        nth L Num Branch Rest,
        place_meta_vars Branch Etree NB (Num::TermPos) Flag,
        nth NL Num NB Rest.
place_meta_vars Term (node _ Pos FEtree AEtree) Term P 1:-
        not (P = Pos).
place_meta_vars Term (node2 _ Pos EtreeL) Term P 1:-
        not (P = Pos).


%%% revise induction

revise_induction (ripGoal (Hyps >>> WaveGoal) NSkel _Embedding) Scheme Subst Rule (seqGoal (H >>> OldGoal)) Sc:-
	induction_schemes_list L,
	embeds_list Embedding NSkel WaveGoal NewSkel NE _ _,
	mappred NE reverse_directions EmbeddingIn,
	repeat_ripple_in (ripGoal (Hyps >>> WaveGoal) NewSkel EmbeddingIn) (ripGoal (Hyps >>> Goal) NewNewSkel NewEmb) Rule,
	printstdout Goal,
	printstdout Rule,
	for_one NewEmb (E\ find_wave_fronts E WFPos _WHPos 0) _,
	memb (hyp (otype_of Var T) _) Hyps,
	subterm_of Goal Var WHPos,
	subterm_of Goal Subterm WFPos,
	subterm_of Subterm Var _,
	memb Scheme L, 
	(not (Scheme = Sc)),
	induction_scheme _  Scheme T Subst _ _ _,
	construct_subst Subterm Var Subst.
%	member_quant Goal Subgoals.
%%%	Worry about this later.
%%%	build_from_address NodeAddress GoalSequence.

local construct_subst osyn -> osyn -> subst -> o.
construct_subst Term1 Term2 (repl Term2 Term1).
construct_subst Term1 Term2 (dom C):-
		construct_subst Term1 Term2 (C _).

local find_wave_fronts etree -> (list int) -> (list int) -> int -> o.
find_wave_fronts (leaf _Dir Pos) WFPos Pos ED:-
		 wave_front Pos ED WFPos.
find_wave_fronts (sink _ Pos) WFPos Pos ED:-
		 wave_front Pos ED WFPos.
find_wave_fronts (node _ _ F A) WFPos WHPos ED:-
		 NED is ED + 1,
		 find_wave_fronts A WFPos WHPos NED.
find_wave_fronts (node2 _ _ EL) WFPos WHPos ED:-
		 NED is ED + 1,
		 for_one EL (E\ find_wave_fronts E WFPos WHPos NED) _.
		 
local wave_front (list int) -> int -> (list int) -> o.
wave_front Pos ED WFPos:-
		 length Pos Depth,
		 Depth > ED,
		 Diff is (Depth - ED),
		 drop_l Diff Pos WFPos.


is_quantifier_in Skel N N.
is_quantifier_in (app forall (tuple [Ty, (abs Prop)])) Nin Nout:-
	N is (Nin + 1),
	pi v\ (is_quantifier_in (Prop v) N Nout).

member_quant X X.
member_quant X (Y ** Z):-
	member_quant X Y,
	member_quant X Z.
member_quant X (allGoal _ G):-
	pi z\ (member_quant X (G z)).

local norule rewrite_rule.
	
repeat_ripple_in (ripGoal (Hyps >>> Goal) Skel E1) ST R:-
	ripple_rewrite _MK Rule Skel (Goal @@ E1) (NewGoal @@ E2) Cond TermPos,
	%% In even proofs even3 loses a wave front - this is measure reducing
	%% whether the wave front is inward or outward, so we want to avoid using this.
	not (R = Rule),
	trivial_condition Cond Hyps,
	embeds_list E2 Skel NewGoal NewSkel NE E1 E1p,
	measure_check red inout NE E1p TermPos Embedding NewSkel Skelp,
	%% for_each Embedding not_zero,
	%% sinkability not needed - we're rippling towards the induction
	%% variable.
	 !,
	repeat_ripple_in (ripGoal (Hyps >>> NewGoal) Skelp Embedding) ST R.
repeat_ripple_in Goal Goal _.

%% reverse direction labels on an embedding.

local rd dir -> dir -> o.
rd inward outward.
rd outward inward.
rd inout inout.

reverse_directions (leaf A Pos) (leaf B Pos):-
		   rd A B.
reverse_directions (sink A Pos) (sink B Pos):-
		   rd A B.
reverse_directions (node A Pos E1 E2) (node B Pos E1P E2P):-
		   rd A B,
		   reverse_directions E1 E1P,
		   reverse_directions E2 E2P.
reverse_directions (node2 A Pos EL) (node2 B Pos ELP):-
		   rd A B,
		   mappred EL reverse_directions ELP.


%%  find_nearest_ind_meth

find_nearest_meth M Address Address:-
	get_method Address Meth, 
	Meth = M, !.
find_nearest_meth M Address Node:-
	parent_address Address NewAddress,
	find_nearest_meth M NewAddress Node.

find_previous_meth M Address Address:-
        retrieve_node Address Plan,
	get_method Address Meth, 
	Meth = M.
find_previous_meth M Address Node:-
	parent_address Address NewAddress,
	find_previous_meth M NewAddress Node.

parent_address (H::Ad) Ad.

%% Lemma speculation


%% Generalisation Critic - tested by qrevcorrect series in list_benchmarks

compound_critic wave (wave_patch (failed_sink Emb G) Ad _Rule)
	(subplan_crit Ad
	(then_crit 
		(generalisation_AI Emb G Lemma) 
 		(then_crit (roll_back_to_crit (induction_meth _ _ _) Address)
	(subplan_crit Address
		(continue_crit 
			(m\ (then_meth (introduce_gen Lemma)
			    (induction_top with_critics)))))))).

atomic_critic wave (generalisation_AI Emb NewGoal QLemma)
	Address
	Agenda
	(get_goal Address (ripGoal (Hyps >>> Conc) Sk Em))
	(not (Conc = trueP),
	construct_generalisation (ripGoal (Hyps >>> Conc) Sk Em) Emb NewGoal Lemma,
	 quantify_lemma Hyps Lemma QLemma)
	nil
	Agenda.

atomic wave (introduce_gen Lemma)
	(seqGoal (Hyps >>> Conc))
	true
	true
	(seqGoal (Hyps >>> Lemma))
	notacticyet.

atomic wave (introduce_lemma Lemma)
	(ripGoal (Hyps >>> Conc) Skel Emb)
	true
	true
	((seqGoal (Hyps >>> Lemma)) ** (ripGoal (((hyp Lemma nha)::Hyps) >>> Conc) Skel Emb))
	notacticyet.

quantify_lemma Hyps Lemma Lemma:-
	(not (member (hyp (otype_of X T) _) Hyps)).
quantify_lemma Hyps Lemma Out :-
	memb_and_rest (hyp (otype_of X T) _) Hyps NewH,
	subterm_of Lemma X _,
	forall_elim X T Lemma NewG,
	(not (subterm_of NewG X _)), !,
	quantify_lemma NewH NewG Out.
quantify_lemma Hyps Lemma Out :-
	memb_and_rest (hyp (otype_of X T) _) Hyps NewH,
	quantify_lemma NewH Lemma Out.

construct_generalisation (ripGoal (Hyps >>> _) Skel _) Emb NewGoal (app forall (tuple [nat, (abs n\ (Out n))])):-
	memb H Hyps,
	memb Sk Skel,
	strip_forall_embeds H _ Sk Sk,
	(H = (hyp H1 _)),
	pi x\ (iterate_wave_fronts x H1 NewGoal (Out x)).
construct_generalisation (ripGoal (Hyps >>> _) Skel _) Emb _
  (app forall (tuple [Type, (abs x\ (app eq (tuple [(GENL x), (GENR x)])))])):-
	memb H Hyps,
	memb Sk Skel,
	strip_forall_embeds H _ Sk Sk,
	Sk = (app eq (tuple [_, _])),
	unsinkable_flag 1 Emb Pos nil,
	(H = (hyp H1 _)),
	(pi x\ 
	    (construct_gen_terms H1 _ x (GENL x) Pos Type 1,
	    construct_gen_terms H1 _ x (GENR x) Pos Type 2)).

construct_generalisation (ripGoal (Hyps >>> _) Skel _) Emb _ (app forall (tuple [Type, (abs x\ (GEN x))])):-
	memb Term Hyps,
	memb Sk Skel,
	strip_forall_embeds Term _ Sk Sk,
	(not (Sk = (app eq (tuple [LHS, RHS])))),
	unsinkable_flag 1 Emb Pos nil,
	(Term = (hyp T1 _)),
	(pi x\ (construct_gen_terms T1 _ x (GEN x) Pos Type 0)).

construct_gen_terms (app forall (tuple [Type, (abs x\ (Term x))])) OT Var 
	(app forall (tuple [Type, (abs x\ (Gen x))])) Pos Ty N:- !,
	pi x\ (construct_gen_terms (Term x) OT Var (Gen x) Pos Ty N).
construct_gen_terms SuperTerm _ Var Gen Pos Type 0:- !,
	subterm_of SuperTerm Term Pos,
	subterm_of Term C _,
	has_otype_ C Ty,
	(not (Ty = (_ arrow _))),
	gen_term Var Term SubGen Type,
	replace_at SuperTerm SubGen Gen Pos.
construct_gen_terms (app eq (tuple [LHS, RHS])) _ Var Gen Pos Type 1:- !,
	construct_gen_terms LHS RHS Var Gen Pos Type 1.
construct_gen_terms (app eq (tuple [LHS, RHS])) _ Var Gen Pos Type 2:- !,
	construct_gen_terms RHS LHS Var Gen Pos Type 2.
construct_gen_terms LHS OT Var Gen Pos Type N:-
	reverse Pos (2::(N::RevPos)),
	reverse RevPos SubPos, 
	!, 
	subterm_of LHS Term SubPos,
	subterm_of Term C _,
%	(not (subterm_of Term OT _)), % This case covered by generalisation mthd.
	has_otype_ C Ty,
	(not (Ty = (_ arrow _))),
	gen_term Var Term SubGen Type,
	replace_at LHS SubGen Gen SubPos.
construct_gen_terms SuperTerm _ Var Gen _ Type _:-
	gen_term Var SuperTerm Gen Type.

gen_term Var Term (app F Var) Type:-
	obj_atom Term, 
	has_otype_ Term Type, 
	!.
gen_term Var Term (app F (tuple [Term, Var])) _.
	

unsinkable_flag 0 (leaf outward _) _ _.
unsinkable_flag X (leaf inward _) Pos Pos.

% Inwards wave front
unsinkable_flag X (node inward _ F E) Pos Pos:-
        % Check subterm
        unsinkable_flag 0 E _ (2::Pos),
        unsinkable_flag 0 F _ (1::Pos).

% Outward wave front
unsinkable_flag 1 (node outward _ F E) Pos PosIn:-
        (unsinkable_flag 1 E Pos (2::PosIn);
        unsinkable_flag 1 F Pos (1::PosIn)).
unsinkable_flag 0 (node outward _ F E) _ PosIn:-
        unsinkable_flag 0 E _ (2::PosIn),
        unsinkable_flag 0 F _ (1::PosIn).

%node2 direction is ignored (assumed to be same surrounding noe)
unsinkable_flag 1 (node2 _ _ Elist) Pos PosIn:-
        % Check Subterms
        nth Elist N E Rest,
        unsinkable_flag 1 E Pos (N::PosIn).
unsinkable_flag 0 (node2 _ _ Elist) _ PosIn:-
        % Check Subterms
        mapcount Elist (Y\ H1\ H2\ N\ (unsinkable_flag 0 Y _ (N::PosIn))) _ _ 1.

/*iterate_wave_fronts A B C D:-
	printstdout A,
	printstdout B,
	printstdout C,
	printstdout D, fail. */
iterate_wave_fronts _ wild_card T T.
iterate_wave_fronts _ T T T.
iterate_wave_fronts X Y (app F Y) (app (app fun_iter (tuple [X, F])) Y).
iterate_wave_fronts X Y (app F Z) (app (app fun_iter (tuple [X, (app fun_compose (tuple [F, H]))])) Y):-
	iterate_wave_fronts X Y Z (app (app fun_iter (tuple [X, H])) Y).
iterate_wave_fronts N (app F X) (app G Y) (app FOut Out):-
	iterate_wave_fronts N F G FOut,
	iterate_wave_fronts N X Y Out.
iterate_wave_fronts X (tuple L) (tuple M) (tuple N):-
	mappred2 L (iterate_wave_fronts X) M N.
iterate_wave_fronts N (abs X) (abs Y) (abs Z):-
	pi x\ (iterate_wave_fronts N (X x) (Y x) (Z x)).
	

compound_critic wave (wave_patch (failed_embed Rule) Ad _Rule)
        (subplan_crit Ad
        (then_crit 
                (previous_casesplit Rule) 
	(subplan_crit Ad
		(continue_crit 
	       (m\ (then_meth post_ripple (induction_top with_critics))))))).

atomic_critic wave (previous_casesplit Rule)
	      Ad
	      Agenda
	      (rewr Rule _ _ _ C,
	       not (C = trueP),
	       find_previous_meth (wave_case_split R2) Ad _,
	       rewr R2 _ _ _ C2,
	   (C2 = (app neg C); C = (app neg C2);
	   (C2 = (app eq (tuple [A, B])), C = (app neq (tuple [A, B])));
	   (C = (app eq (tuple [A, B])), C2 = (app neq (tuple [A, B])))))
	   true
	   nil
	   Agenda.
		   

end
