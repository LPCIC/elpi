module rob030.

accumulate lkf-kernel.
accumulate eprover.
accumulate resolution_steps.

resProblem "rob030" [(pr 2 (n ((add c d) == d)) ),
(pr 1 (all (X1\ (all (X2\ (p ((negate (add X1 X2)) == (negate X2))))))) )] 
(resteps [pm (id (idx 1)) (id (idx 2)) 0])
 (map [
pr 1 (all (X1\ (all (X2\ (p ((negate (add X1 X2)) == (negate X2))))))),
pr 0 f-,
pr 2 (n ((add c d) == d))
]).

inSig negate.
inSig add.


