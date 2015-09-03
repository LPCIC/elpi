/*
 * Implementation of some tacticals, i.e. `programs' for combining 
 * primitive tactics in a way that yields derived rules.
 */

module tacticals.

accum_sig  goaltypes.

accumulate  goalred.

type    maptac          (goal -> goal -> o) -> goal -> goal -> o.
type    then            (goal -> goal -> o)
                          -> (goal -> goal -> o) -> goal -> goal -> o.
type    orelse          (goal -> goal -> o)
                          -> (goal -> goal -> o) -> goal -> goal -> o.
type    idtac           goal -> goal -> o.
type    repeattac       (goal -> goal -> o) -> goal -> goal -> o.
type    try             (goal -> goal -> o) -> goal -> goal -> o.
type    complete        (goal -> goal -> o) -> goal -> goal -> o.


%  maptac will map a tactical over a compound goal structure.  This
%  is useful since we only need to have primitive tactics work on
%  primitive goals.
maptac Tac truegoal truegoal.
maptac Tac (andgoal InGoal1 InGoal2) OutGoal :-
  maptac Tac InGoal1 OutGoal1,
  maptac Tac InGoal2 OutGoal2,
  goalreduce (andgoal OutGoal1 OutGoal2) OutGoal.
maptac Tac (allgoal InGoal) OutGoal :-
  pi T\ (maptac Tac (InGoal T) (OutGoal1 T)),
  goalreduce (allgoal OutGoal1) OutGoal.
maptac Tac InGoal OutGoal :-
  Tac InGoal OutGoal.


%  The next three clauses define three familar and basic tactics.
then Tac1 Tac2 InGoal OutGoal :-
  Tac1 InGoal MidGoal,
  maptac Tac2 MidGoal OutGoal.

orelse Tac1 Tac2 InGoal OutGoal :-
  Tac1 InGoal OutGoal,!;
  Tac2 InGoal OutGoal.

idtac Goal Goal.


% The next three clauses define certain other useful tacticals.
repeattac Tac InGoal OutGoal :-
  orelse (then Tac (repeattac Tac)) idtac InGoal OutGoal.

try Tac InGoal OutGoal :-
  orelse Tac idtac InGoal OutGoal.

complete Tac InGoal truegoal :-
  Tac InGoal truegoal.
