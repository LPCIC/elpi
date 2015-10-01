/*

File: goal.mod
Author: Louise Dennis / James Brotherston
Description: Support for goals, sequents and queries in lclam
Last Modifed: 13th August 2002

*/

module goal.

reduce_goal trueGoal trueGoal.
reduce_goal (trueGoal ** X) Y :- reduce_goal X Y, !.
reduce_goal (X ** trueGoal) Y :- reduce_goal X Y, !.
reduce_goal (X ** Y) Z :- reduce_goal X XX, reduce_goal Y YY, 
                          reduce_goal (XX ** YY) Z.
reduce_goal (_X vv trueGoal) trueGoal.   % backtracking?
reduce_goal (trueGoal vv _Y) trueGoal.   % also ??
reduce_goal (allGoal _ G) H :-
   pi i\ (reduce_goal (G i) H).
reduce_goal (existsGoal _ G) H :-
   pi i\ (reduce_goal (G i) H).         % if goal does not depend

list2goal nil trueGoal.
list2goal (X::nil) X.
list2goal (X::(Y::T)) (X ** G):-
	list2goal (Y::T) G.

compound_goal trueGoal.
compound_goal falseGoal.
compound_goal (allGoal _ _).
compound_goal (existsGoal _ _).
compound_goal (_ ** _).

end
