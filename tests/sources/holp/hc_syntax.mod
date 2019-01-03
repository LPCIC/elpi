/* 
 * Predicates that recognize goal and clause structure in the logic of 
 * Horn clauses. This code illustrates how recursion over abstraction 
 * structure is programmed in Lambda Prolog
 */

module  hc_syntax.

goal tru.
goal (B and C) :- goal B, goal C.
goal (B or C)  :- goal B, goal C.
goal (some C) :- pi X \ ((termp X) => (goal (C X))).
goal A :- atom A.

def_clause (all C)   :- pi X \ ((termp X) => (def_clause (C X))).
def_clause (G imp A) :- atom A, goal G.
def_clause A :- atom A.
