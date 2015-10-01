/*

File: generalise.mod
Author: Louise Dennis
Description: The generalise method.
Last Modifed: 7th March 2001

*/

module generalise.

accumulate logic_eq_constants.

local   gener           goal -> osyn -> goal -> o.
                                     % subterm appropriate for generalisation,
                                     % giving new sequent
local   quantify_gener  goal -> goal -> o.
local   compound_gen    osyn -> o.


atomic gen generalise
        InG
        ( gener InG T NewGoal )
        true 
	NewGoal 
	notacticyet.


gener (seqGoal (H >>> (app eq (tuple [A, B])))) T   
      (seqGoal (H >>> (app forall (tuple [Type,
		(abs v\ (app eq (tuple [(NewA v), (NewB v)])))])))) :-
                A = (NewA T),
                compound_gen T,
                B = (NewB T), 
               	not ( NewA = (x\ _AA)),
                not ( NewB = (x\ _BB)),
                env_otype T H Type,
                env_otype (NewA T) ((hyp (otype_of T Type) nha)::H) _.

% infer object type for generalisation
gener (seqGoal (H >>> (app forall (tuple [Ty, (abs Body)])))) (abs T)
      New :-
	( pi X\ (gener (seqGoal (((hyp (otype_of X Ty) nha) :: H) >>> (Body X))) (T X)
                       (seqGoal (((hyp (otype_of X Ty) nha) :: H) >>> (NewBody X)))
                )
        ),
      quantify_gener (seqGoal (H >>> (app forall (tuple [Ty, (abs NewBody)])))) New.

% mode: quantify_gener + -
%
% If generalisation results in one of the goal's universally quantified 
% variables being deleted from the goal, then omit the corresponding
% quantifier, i.e. introduce the quantifier and thin the newly introduced
% constant away.
% '
quantify_gener (seqGoal (H >>> (app forall (tuple [_, (abs x\ NewBody)]))))
               (seqGoal (H >>> NewBody)).

quantify_gener (seqGoal (H >>> (app forall (tuple [Ty, (abs x\ (NewBody x))]))))
               (seqGoal (H >>> (app forall (tuple [Ty, (abs x\ (NewBody x))])))).

compound_gen (app _ _).

end
