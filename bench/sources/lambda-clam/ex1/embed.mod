/*

File: embed.mod
Author: Louise Dennis / James Brotherston
Description:  Embeddings (as used by rippling)
Last Modified: 20th August 2002

*/

module embed.

accumulate logic_eq_constants.


% ***************************************************************************
%                                                                           *
%                           AUXILIARY SYMBOLS                               *
%                                                                           *
% ***************************************************************************

local merge_weights  (list int) -> (list (list int)) -> (list int) -> o.

local get_weight  etree -> (list int) -> (list int) -> o.
local get_wt etree -> dir -> (list int) -> int -> o.

local tweak_directions etree -> etree -> dir -> o.

local measure_less (list int) -> (list int) -> (list int) -> (list
int) -> o.
local lexicographic_less (list int) -> (list int) -> o.
local reverse_lexicographic_less (list int) -> (list int) -> o.

local embedding     etree -> osyn -> osyn -> (list int) -> o.

local find_moved_wave_fronts  (etree -> etree -> etree -> int -> int -> o).
local no_direction_change (list int) -> (list int) -> int -> int -> int -> int -> int -> o.

/*
local chooseDirFlag dir -> dir -> dir -> o.
*/
local label_wave_fronts etree -> int -> etree -> o.

localkind wffl type.

local wfflag dir -> wffl -> dir.
local iswf wffl.
local notwf wffl.
%***************************************************************************
%
% embeds is just the interface to embedding:
%
%
% LD - experimentally inserting a cut to see if this will stop repeate
% success of set_up_ripple - worried this may ultimately need to be removed 
% again
embeds X Y Z :- 
%       on_backtracking (printstdout "failed"),
    embedding X Y Z nil, !.

% **************************************************************************
% 
%			  MAIN EMBEDDING CODE
%
% **************************************************************************
%

% embedding -Embedding +Skel +Waveterm +Address
%
% Embed the skeleton Skel in the wave term Waveterm. In any call to
% embedding/4, the Address argument is the position in the of Waveterm
% term in wave term which was given as the third argument to the outermost
% call of embedding/4 - each time we step down through the waveterm,
% address gets one longer. In order for the measure-calculation code
% to work correctly, we should not embed a function term f(t_1,...,t_n)
% in a term e, but should separately embed f, and then each of the t_i in
% e, so that the nodes in the embedding tree are only one functor thick.
%
%
% Should add sinkability condition so that a wave front can only become
% inwards directed if the term it is attached to, or on of its subterms,
% matches a sink in the induction hypothesis.
%
% Is there any way to merge embedding with measure calculation? 
%
% Embeddings are defined by the following rules:
%
%        t < u_i
%   ------------------
%   t < f(u_1,...,u_n) 
%
%       t_1 < u_1,..., t_n < u_n
%   ---------------------------------
%    f(t_1,...,t_n) < f(u_1,...,u_n)
%
%           (P v) < (Q v),   v fresh          Note that when this rule is
%   ---------------------------------         used, the rule immediately
%        (x\ P x) < (y\ Q y)                  below will also be used.
%      
%            P < (Q v),   v fresh
%   ---------------------------------
%          P  < (y\ Q y)
%
%        x ground, V meta-variable            Note that V is not bound
%   ----------------------------------        to x by this rule.
%                x < V
%   
%                x < x
%
%           wild_card < t                     A sink can embed in any term
%


%             V meta-variable                 Note that V is never bound
%   ----------------------------------        to x by this rule. x may
%                x < V                        also be a meta-variable.
%

/*
embedding T X Y Ad:-
	  printstdout T,
	  printstdout X,
	  printstdout Y, 
	  fail.
*/

embedding (leaf Dir Ad) X Y Ad :-
	(%(Dir = inout); 
	(Dir = outward); (Dir = inward)),
%%%% CHANGED FROM MVAR
    headvar_osyn Y,
    ((headvar_osyn X); ((not (X = wild_card)), obj_atom X)), 
  	!.

%***************************************************************************
%
%                     Base case - any term embeds in itself
%     x < x
%
%% Placed this hear so that variables introduced by removing foralls
%% in hyp embed in conclusion if it is a variable.
embedding  (leaf Dir1 Ad) X Y Ad :- 
%%%% CHANGED FROM MVAR
	((headvar_osyn X); (obj_atom X,
	(not (X = wild_card)))),
	(Y = X),
	(headvar_osyn X; obj_atom X),
        !,
	(%(Dir1 = inout); 
	(Dir1 = outward); (Dir1 = inward)).


%% A sink is a variable - this will have been given a type by the
%% embed theory not by a "real" theory.

embedding (sink Dir1 Ad) X Y Ad :-
	(not (headvar_osyn X)),
	X = wild_card,
%	obj_atom Y,
%	Do we want sinks at leafs of erasure?
%	YES ABSOLUTELY - check out less_double_mono
	not (headvar_osyn Y),
        obj_atom Y,
	(%(Dir1 = inout); 
	(Dir1 = outward); (Dir1 = inward)).

%% distinguish between a sink which has expanded and one that hasn't.  
%% Distinction needed for less_double_mono among other thms.
embedding (sink Dir1 Ad) X Y Ad :-
	(not (headvar_osyn X)),
	X = wild_card,
%	obj_atom Y,
%	Do we want sinks at leafs of erasure?
%	YES ABSOLUTELY - check out less_double_mono
	headvar_osyn Y,
	(%(Dir1 = inout); 
	(Dir1 = outward); (Dir1 = inward)).

embedding _ X Y _ :-
  ((headvar_osyn Y); (headvar_osyn X)),
  !, fail.

%***************************************************************************
%
%                 Descend into lambda abstractions.
%
%
%
%           (P v) < (Q v),   v fresh          Note that when this rule is
%   ---------------------------------         used, the rule immediately
%        (x\ P x) < (y\ Q y)                  below will also be used.
%      
embedding T (abs X) (abs Y) Ad :-
    pi z \ (has_otype embed z Type => embedding T (X z) (Y z) Ad).


%            P < (Q v),   v fresh
%   ---------------------------------
%          P  < (y\ Q y)
%
embedding T X (abs Y) Ad :-
    pi z \ (has_otype embed z Type => embedding T X  (Y z) Ad).


%
% JIHG - special clauses for embedding forall's
%
% Give object-level types to the anon constants that stand in for the
% universal variable.  This allows wild_card2's to be embedded in them.
%
embedding (node Dir1 Ad (leaf Dir1 (1::Ad)) (node2 Dir2 (2::Ad) ((leaf Dir3 (1::1::Ad))::E::nil)))
          (app forall (tuple [Type, (abs X)]))
          (app forall (tuple [Type, (abs Y)])) Ad :-
%%%% CHANGED FROM MVAR
	pi z\ (has_otype embed z Type => embedding E (X z) (Y z) (2::2::Ad)), !,
	(%(Dir1 = inout); 
	(Dir1 = outward); (Dir1 = inward)),
	(%(Dir2 = inout); 
	(Dir2 = outward); (Dir2 = inward)),
	(%(Dir3 = inout); 
	(Dir3 = outward); (Dir3 = inward)).

embedding E X
          (app forall (tuple [Type, (abs Y)])) Ad :-
	pi z\ (has_otype embed z Type => embedding E X (Y z) (2::2::Ad)).



%***************************************************************************
%
%            Embed all the arguments of two identical functions.
%
% The directions of the wave fronts in the arguments of f are set to 
% be the same as the direction of the wave fronts of f if the embedding
% and embedded terms could unify. This seems to be a slight restriction of
% embeddings, but improves efficiency.
% 
%
%       t_1 < u_1,..., t_n < u_n
%   ---------------------------------
%    f(t_1,...,t_n) < f(u_1,...,u_n)
%

embedding (node Dir1 Ad Ftree Etree) (app F X) (app Fout Y) Ad :-
%%%% CHANGED FROM MVAR
	((headvar_osyn F); (not (F = forall))),
     embedding Ftree F Fout (1::Ad),
     embedding Etree X Y (2::Ad), !,
	(%(Dir1 = inout); 
	(Dir1 = outward); (Dir1 = inward)).



%***************************************************************************
%
%        Embed the first term in one of the arguments of the second term
%
%
%        t < u_i
%   ------------------
%   t < f(u_1,...,u_n) 
%
embedding E T (app F Y) Ad :-
    embedding E T F (1::Ad).
embedding E T (app F Y) Ad :-
    embedding E T Y (2::Ad).

% Tuples
embedding (node2 Dir1 Ad T) (tuple X) (tuple L) Ad :-
%%%% CHANGED FROM MVAR
    mapcount T 
          (H\ H1\ H2\ C\ (embedding H H1 H2 (C::Ad))) X L 1, !,
	((Dir1 = outward); (Dir1 = inward)).

embedding T X (tuple L) Ad :- 
    nth L Num F _Rest,
    embedding T X F (Num::Ad).   


%***************************************************************************
%
%                   A sink can embed in any term.
%
%
%     wild_card < t
%
% Don't return Any in embedding tree, since this could violate binding
% constraints.

%***************************************************************************
%
% Do not apply to function terms when we know the functor (what about
% terms with flexible head?)


%***************************************************************************
%
%	MEASURE CODE
%
%***************************************************************************
%
%               Now we define a measure on embeddings.
%
% The embeddings to be compared are first flattened into lists of
% weights (which are natural numbers).

% Outward weights are compared first and then inward weights.

%% Outward weights compared with reverse lexicographic order.
%% Inward weights compared with lexicographic order.

% Unfortunately we can't leave directions as variables on generation
% so we need to mark variable weights as inout and then revise making
% as many outward weights as possible since these can be turned
% inward.

% I'm not sure the previously used inout marker is really needed.

check_measure_reducing MKey outward NewEmbedding OldEmbedding _TermPos NewNewEmbedding:-
	match_directions OldEmbedding NewEmbedding NewNewEmbedding,
	get_weight OldEmbedding OldOutward OldInward, 
	get_weight NewNewEmbedding NewOutward NewInward, 
	reverse_lexicographic_less NewOutward OldOutward, 
	!.
check_measure_reducing MKey inout NewEmbedding OldEmbedding TermPos EmbeddingOut:-
	not (NewEmbedding = dummytree),
	match_directions OldEmbedding NewEmbedding NNewEmbedding,
	get_weight OldEmbedding OldOutward OldInward,
	find_moved_wave_fronts OldEmbedding NNewEmbedding NewNewEmbedding 0 0, !,
	%% Get all possible directional annotations for Embedding
	label_wave_fronts NewNewEmbedding 0 NewEmb,
	%% Find all directional labels on wave fronts and sort in
	%% order of the measure - aim is to pick the greatest embedding
	%% which reduces wrt the old embedding.
	findall_sort
		     (E\ tweak_directions NewEmb E outward)
		     Es
	     (E2\ E1\ (sigma NO1\ sigma NO2\ sigma NI1\ sigma NI2\
                      (get_weight E1 NO1 NI1, 
		       get_weight E2 NO2 NI2,
		       measure_less NO1 NO2 NI1 NI2))), !,
	memb EmbeddingOut Es,
	get_weight EmbeddingOut NewOutward NewInward,
	measure_less NewOutward OldOutward NewInward OldInward.

local match_directions etree -> etree -> etree -> o.
match_directions (leaf Dir _) (leaf _Dir Pos) (leaf Dir Pos).
match_directions (sink Dir _) (sink _Dir Pos) (sink Dir Pos).
match_directions (node Dir _ Ftree Etree) (node _Dir Pos F E) (node Dir Pos F1 E1):-
		 match_directions Ftree F F1,
		 match_directions Etree E E1.
match_directions (node2 Dir _ EtreeL) (node2 _Dir Pos EL) (node2 Dir Pos EL1):-
		 mappred2 EtreeL match_directions EL EL1.

/*
not_zero Embedding:-
	 get_weight Embedding _ Inward,
	 for_each Inward (x\ (not (X = 0))).
*/

%% Weight comparison code.
measure_less Out Out NewIn OldIn:-
	!,
	lexicographic_less NewIn OldIn, !.
measure_less NewOut OldOut _ _:-
	reverse_lexicographic_less NewOut OldOut, !.

lexicographic_less (H::_) (H1::_) :-
	H < H1, !.
lexicographic_less (H::T) (H::T1):-
	!,
	lexicographic_less T T1.

reverse_lexicographic_less L1 L2:-
	length L1 L,
	length L2 L, !,
	reverse L1 L1R,
	reverse L2 L2R,
	lexicographic_less L1R L2R.
reverse_lexicographic_less L1 L2:-
	length L1 Len1,
	length L2 Len2, 
	Len1 < Len2, !.


%% Weight calculation code
get_weight Embedding Outward Inward:-
	get_wt Embedding outward Outward 0,
	get_wt Embedding inward Inward 0, !.

%% According to TpHOls paper (Smaill & Green, Higher Annotated Terms for
%% proof search) the weight of an embedding node is the difference between
%% the length of the address at that node (Pos below) and the depth
%% in the tree.  I think they mean by this the Depth in the skeleton _but_
%% to get the measure that is analogous to Basin & Walsh's measure we
%% need a subtler notion.  

%% Once a wave front has appeared in the term _everything_ below it
%% that appears in the skeleton will be out by some amount (the extra
%% depth created by the wave front.  In fact we only want the first 
%% skeleton term to be out and everything under it to be out by
%% zero until the next wave front appears.  Therefore we actually 
%% need to keep an artificial count of "TermDepth" which increments
%% everywhere except where a wave front appears and use that for
%% our comparison.  In fact we can take this term Depth to be the
%% Length of the position for the parent embedding node.


get_wt (leaf Dir Pos) Dir (X::nil) TermDepth:-
	!, length Pos Len,
	X is (Len - TermDepth).
%% Directions don't match
get_wt (leaf _Dir _Pos) _Dir2 (0::nil) _.
get_wt (sink Dir Pos) Dir (X::nil) TermDepth:-
	!, length Pos Len,
	X is (Len - TermDepth).
get_wt (sink _Dir _Pos) _Dir2 (0::nil) _.
get_wt (node Dir Pos Ftree Tree) Dir (X::Measure) TermDepth:-
	!, length Pos Len,
	X is (Len - TermDepth),
	NewTermDepth is (Len + 1),
	(not (Ftree = dummytree)),
	(not (Tree = dummytree)),
	get_wt Tree Dir MA NewTermDepth,
	get_wt Ftree Dir MF NewTermDepth,
	merge_weights nil [MF, MA] Measure.
get_wt (node _Dir2 Pos Ftree Tree) Dir (0::Measure) _TermDepth:-
	(not (Ftree = dummytree)),
	(not (Tree = dummytree)),
	length Pos Len,
	NewTermDepth is (Len + 1),
	get_wt Ftree Dir MF NewTermDepth,
	get_wt Tree Dir MA NewTermDepth,
	merge_weights nil [MF, MA] Measure, !.
get_wt (node2 Dir Pos TreeList) Dir (X::Measure) TermDepth:-
	!, length Pos Len,
	X is (Len - TermDepth),
	NewTermDepth is (Len + 1),
	mappred TreeList (X\ Y\ ((not (X = dummytree)), 
                          get_wt X Dir Y NewTermDepth)) MeasureList,
	merge_weights nil MeasureList Measure.
get_wt (node2 _Dir2 Pos TreeList) Dir (0::Measure) _TermDepth:-
	length Pos Len,
	NewTermDepth is (Len + 1),
	mappred TreeList (X\ Y\ ((not (X = dummytree)), get_wt X Dir Y NewTermDepth)) MeasureList,
	merge_weights nil MeasureList Measure, !.

merge_weights nil (H::T) Y:-
	merge_weights H T Y.
merge_weights X nil X.
merge_weights W1 (W2::R2) R :-
	((pi mw_aux\
		(pi Y\ mw_aux  nil Y Y,
		 pi X\ mw_aux X nil X,
		 pi X\ pi Y\ pi W\ pi R1\ pi R2\ pi R\
			(mw_aux ((X:int)::R1) ((Y:int)::R2) ((W:int)::R) :-
      				W is X + Y, mw_aux R1 R2 R)) =>
	 mw_aux W1 W2 W)),
      	merge_weights W R2 R.
	
%%  By convention all nodes below a wave front and until the next
%%  wave front occurs are labelled as that wave front.

%% inward nodes may turn outward and allow the possibility of a node
%% further down the branch turning inward - this is controlled by DirFlag.

%% temporariliy each direction is paired with a flag saying whether that
%% node in the embedding is a wave front or not.

%% Originally this produced all possible annotations of the wave fronts
%% however we need to prevent outward wavefronts going back in again

%% Suppose nodes which have either gained or lost a wave front
%% are left uninstantiated - so their direction can be changed.

%% If we come to a moved node - which is a wavefront and so far
%% no wave fronts higher up the tree have been added or removed
%% then this wave front can be outward moving or inward moving

%% If we come to a moved node - which is not a wavefront and so far
%% no wave fronts higher up the tree have been added or removed
%% then this node must be outward. 

%% If we come to a moved node which is a wavefront under a moved
%% node which is not a wave front, then this node must be
%% inward and only if it was previously labelled inward.

%% Seem to have done this in find_moved_wave_fronts
%% Have a flag 0 -> a new wave front has appeared above this
%%                  and I don't know where it came from
%%             1 -> a wave front has been lost above this and
%%                  I don't know where it went
%%             2 -> no unaccounted for wave fronts


tweak_directions (leaf (wfflag Dir  notwf) Pos) (leaf WFDir Pos) WFDir.
/*
tweak_directions (leaf (wfflag inward  iswf) Pos) (leaf inward Pos) _ 1.
		 %% This can only be inwards and only if 
                 %%it was inwards already. 
*/
tweak_directions (leaf (wfflag Dir iswf) Pos) (leaf Dir1 Pos) _ :-
	((Dir = inout, (Dir1 = outward; Dir1 = inward)) ;
	 (not (Dir = inout), (Dir = Dir1))).
tweak_directions (sink (wfflag Dir  notwf) Pos) (sink WFDir Pos) WFDir.
/*
tweak_directions (sink (wfflag inward  iswf) Pos) (sink inward Pos) _ 1.
		 %% This can only be inwards and only if 
                 %%it was inwards already. 
*/
tweak_directions (sink (wfflag Dir iswf) Pos) (sink Dir1 Pos) _ :-
	((Dir = inout, (Dir1 = outward; Dir1 = inward)) ;
	 (not (Dir = inout),(Dir = Dir1))).
tweak_directions (node (wfflag Dir  notwf) Pos Ftree Etree) (node WFDir Pos Ftree1 Etree1) WFDir:-
	tweak_directions Ftree Ftree1 WFDir,
	tweak_directions Etree Etree1 WFDir.
/*
tweak_directions (node (wfflag Dir  iswf) Pos Ftree Etree) (node Dir1 Pos Ftree1 Etree1) _ 2:-
	((Dir = inout, (Dir1 = outward; Dir1 = inward)) ;
	 (not (Dir = inout), (Dir = Dir1))),
	tweak_directions Ftree Ftree1 Dir 1,
	tweak_directions Etree Etree1 Dir 1.
tweak_directions (node (wfflag Dir  iswf) Pos Ftree Etree) (node Dir Pos Ftree1 Etree1) _ 1:-
	(Dir = outward; Dir = inward),
	tweak_directions Ftree Ftree1 Dir 1,
	tweak_directions Etree Etree1 Dir 1.
*/
tweak_directions (node (wfflag Dir  iswf) Pos Ftree Etree) (node Dir1 Pos Ftree1 Etree1) _ :-
	((Dir = inout, (Dir1 = outward; Dir1 = inward)) ;
	 (not (Dir = inout), (Dir = Dir1))),
	tweak_directions Ftree Ftree1 Dir1,
	tweak_directions Etree Etree1 Dir1.
%% Tuples should not be wave fronts
tweak_directions (node2 (wfflag Dir  notwf) Pos EtreeL) (node2 WFDir Pos EtreeL1) WFDir:-
	 mappred EtreeL (E\ E1\ tweak_directions E E1 WFDir) EtreeL1.

/*
chooseDirFlag outward outward outward.
chooseDirFlag inward outward inward. % all lower wfs must be inward.

%% wave front has changed direction
chooseDirFlag outward inout inout.  % an inward wf has moved in.

chooseDirFlag inward inward inward. % we're wanting an inward and have one.
chooseDirFlag outward inward inout.
*/

%% find_moved_wave_fronts
%% This is supposed to determine the places where the embedding direction
%% Can change.  This has turned out to be rather complex.
%% As I see it.  An embedding has changed if the position it embeds into
%% has changed.  But life is more complex that this.  Suppose somewhere 
%% above it the position changed then the change could be just because of this
%% higher address shift.
%% Furthermore, traditionally, we only want the direction to change if the
%% wave front has moved "sideways" we don't want to start rippling back
%% in the way we just came.

%% In terms of embeddings.  Suppose first we have detected genuine movement
%% (I'll come to this in a minute) then either three things may have happened
%% the address may be a shorter wrt. to its parent - the wave 
%% front width has closed, i.e. a 
%% wave front has moved elsewhere in the tree.  It may be a superstring 
%% (or equal) - in 
%% which case a wave front has moved here from somewhere else directly 
%% above - or it may
%% be longer or equal and non-comparable - this might be caused
%% by a communtativity lemma - the wave front has moved to a different branch 
%% of the erasure.  I suggest that in cases one and two the direction should
%% not be allowed to change only in case three should it.

%% experimental: I've added that the length of the old wave front must
%% have been one (i.e. it was not a wave front - to prevent manipulation
%% within wavefronts allowing their directions to change.  Not sure about
%% this but it was affecting the proof of doubletimes (among others).

%% In terms of movement above an embedding effecting changes, I suggest
%% that only embeddings which have alterd wrt. their immediate parent
%% should be considered as candidates for moved wave fronts.  All
%% we need to know is the length of the parent nodes and delete that from
%% the end of the position information.

%% Problem with filapp.  I'm going to try "if a wave front has
%% reduced (i.e. moved elsewhere) then the directions below the wave front
%% should remain fixed".

%% embedding direction should not change
find_moved_wave_fronts (node OldDir Pos OFT OEtree) 
			(node _ NewPos NFT NEtree)
			(node OldDir NewPos NNFT NNEtree) OldP NewP:-
	no_direction_change Pos NewPos OldP NewP OP NP Flag, !,
	(not (NFT = dummytree)),
	(not (NEtree = dummytree)),
	find_moved_wave_fronts OFT NFT NNFT OP NP,
	((Flag = 0, find_moved_wave_fronts OEtree NEtree NNEtree OP NP);
	 (NNFT = NFT, NEtree = NNEtree)), !.
find_moved_wave_fronts (node _ Pos OFT OEtree) 
			(node _ NewPos NFT NETree)
			(node _ NewPos NNFT NNEtree) _DisP _:-
	(not (NFT = dummytree)),
	(not (NETree = dummytree)),
	length Pos OP,
	length NewPos NP,
	find_moved_wave_fronts OFT NFT NNFT OP NP,
	find_moved_wave_fronts OEtree NETree NNEtree OP NP, !.
find_moved_wave_fronts (node2 OldDir Pos OEtreeL) (node2 _ NewPos NEtreeL)
			(node2 OldDir NewPos NNEtreeL) OldP NewP:-
	%% There should never be a change in direction at node2s since
	%% they are sugar.
	length Pos OP,
	length NewPos NP,
	mappred2 OEtreeL (OE\ NE\ NNE\ 
		((not (NE = dummytree)),
		find_moved_wave_fronts OE NE NNE OP NP))
		 NEtreeL NNEtreeL, !.
find_moved_wave_fronts (leaf OldDir Pos) (leaf _ NewPos) 
		(leaf OldDir NewPos) OldP NewP:-
	no_direction_change Pos NewPos OldP NewP OP NP _, !.
find_moved_wave_fronts (leaf _ Pos) (leaf _ NewPos) (leaf _ NewPos) _ _.
find_moved_wave_fronts (sink OldDir Pos) (sink _ NewPos) 
		(sink OldDir NewPos) OldP NewP:-
	no_direction_change Pos NewPos OldP NewP OP NP _,
	!.
find_moved_wave_fronts (sink _ Pos) (sink _ NewPos) (sink _ NewPos) _ _.

%% Flag used to signal when position below should not change.
no_direction_change Pos NewPos OldP NewP OP NP Flag:- 
	reverse Pos Pos1,
	reverse NewPos NewPos1,
	drop_l OldP Pos1 P1,
	drop_l NewP NewPos1 NP1,
	length Pos OP,
	length NewPos NP,
	ODiff is (OP - OldP),
	NDiff is (NP - NewP),
	((ODiff > NDiff, Flag = 1); not (ODiff = 1); P1 = NP1).

label_wave_fronts (leaf Dir Pos) TermDepth (leaf NewDir Pos):-
	length Pos Len,
	X is (Len - TermDepth),
	((X = 0, NewDir = (wfflag Dir  notwf));
         ((not (X = 0)), NewDir = (wfflag Dir iswf))), !.
label_wave_fronts (sink Dir Pos) TermDepth (sink NewDir Pos):-
	length Pos Len,
	X is (Len - TermDepth),
	((X = 0, NewDir = (wfflag Dir  notwf));
         ((not (X = 0)), NewDir = (wfflag Dir iswf))), !.
label_wave_fronts (node Dir Pos Ftree Tree) TermDepth (node NewDir Pos NF NT):-
	!, length Pos Len,
	X is (Len - TermDepth),
	((X = 0, NewDir = (wfflag Dir  notwf));
         ((not (X = 0)), NewDir = (wfflag Dir iswf))),
	NewTermDepth is (Len + 1),
	label_wave_fronts  Ftree NewTermDepth NF,
	label_wave_fronts  Tree NewTermDepth NT, !.
label_wave_fronts (node2 Dir Pos TreeList) TermDepth (node2 NewDir Pos NTL):-
	!, length Pos Len,
	X is (Len - TermDepth),
	((X = 0, NewDir = (wfflag Dir  notwf));
         ((not (X = 0)), NewDir = (wfflag Dir iswf))),
	NewTermDepth is (Len + 1),
	mappred TreeList (X\ Y\ ((not (X = dummytree)), 
                          label_wave_fronts X NewTermDepth Y)) NTL, !.
end
