/*
 * An interpreter for the logic of Horn clauses. This code illustrates 
 * the usefulness of beta reduction in realizing substitution. Also note
 * the use of the logic variable in the third clause for try_clause.
 */

module  hc_interp.

accumulate lists.

type   backchain   (list form) -> form -> o.
type   try_clause  (list form) -> form -> form -> o.

hc_interp Cs (some B)  :- !, hc_interp Cs (B T).
hc_interp Cs (B and C) :- !, hc_interp Cs B, hc_interp Cs C.
hc_interp Cs (B or C) :- !, (hc_interp Cs B ; hc_interp Cs C).
hc_interp Cs A  :-  backchain Cs A.

backchain Cs A :- memb D Cs, try_clause Cs D A.

try_clause Cs (D1 and D2) A :- 
     !, (try_clause Cs D1 A ; try_clause Cs D2 A).
try_clause Cs (all D) A :- !, try_clause Cs (D T) A. 
try_clause Cs A A.
try_clause Cs (G imp A) A :- hc_interp Cs G.

