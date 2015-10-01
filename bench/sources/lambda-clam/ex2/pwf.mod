/*

File: pwf.mod
Author: Louise Dennis
Description: Piecewise Fertilisation as described in BBNote 1286
Created:  October 7th 2002

*/

module pwf.

accumulate wave.

local memb_under_forall osyn -> (list osyn) -> o.

atomic pwf imp_ifert
        (ripGoal (Hyps >>> (app imp (tuple [Ap, Bp]))) _Skel _E1)
        (induction_hypothesis Hyps H,
	 memb_under_forall (app imp (tuple [A, B])) H ,
	 % should be that A and Ap have the same skeleton but
	 % we have no theory for annotations in the hypotheses
	 embeds EA A Ap,
	 embeds EB B Bp)
        true 
	((ripGoal (((hyp A nha)::Hyps) >>> Ap) [A] [EA]) ** (ripGoal (((hyp B nha)::Hyps) >>> Bp) [B] [EB]))
	notacticyet.

compound pwf piecewise_fertilisation
         (repeat_meth
		imp_ifert)
        _
        true.

memb_under_forall Term ((hyp Term _)::_).
memb_under_forall Term ((hyp (app forall (tuple [_, (abs P)])) _)::T):-
        memb_under_forall Term ((hyp (P A) _)::T).
memb_under_forall Term (_H::T):-
        memb_under_forall Term T.
		  
     

end
