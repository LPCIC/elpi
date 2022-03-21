/*
 * Code for simplifying goals. Currently the only simplification is that
 * of removing trivial goals (truegoal) from larger goal expressions.
 */

module goalred.

accum_sig  goaltypes.

type    goalreduce      goal -> goal -> o.

goalreduce (andgoal truegoal Goal) OutGoal :-
  !, goalreduce Goal OutGoal.

goalreduce (andgoal Goal truegoal) OutGoal :-
  !, goalreduce Goal OutGoal.

goalreduce (allgoal T\ truegoal) truegoal :- !.

goalreduce Goal Goal.
