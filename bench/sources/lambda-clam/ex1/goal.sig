/*

File: goal.sig
Author: Louise Dennis / James Brotherston
Description: Support for goals, sequents and queries in lclam
Last Modifed: 13th August 2002

*/

sig goal.

accum_sig basic_types.

type user_query string -> query.

type trueGoal goal.
type falseGoal goal.
type **       goal -> goal -> goal.     % conjunction
type vv       goal -> goal -> goal.     % disjunction
type allGoal   osyn -> (A -> goal) -> goal.
type existsGoal osyn -> (A -> goal) -> goal.     

type   >>>     (list osyn) -> osyn -> osyn.
type   seqGoal osyn -> goal.  

infix ** 200.
infix vv 200.
infix >>> 100.

%% Support Predicate
type reduce_goal  goal -> goal -> o.

type top_goal theory -> query -> (list osyn) -> osyn -> o.

type list2goal (list goal) -> goal -> o.

type compound_goal goal -> o.

end