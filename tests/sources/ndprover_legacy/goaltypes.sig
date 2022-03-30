/*
 * Encodings for goals in a tactic and tactical style prover; the needed
 * sort and constructors of this sort are identified here
 */

sig  goaltypes.

kind    goal            type.

type    truegoal        goal.
type    andgoal         goal -> goal -> goal.
type    allgoal         (A -> goal) -> goal.


