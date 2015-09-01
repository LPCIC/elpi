module col052.

accumulate lkf-kernel.
accumulate eprover.
accumulate resolution_steps.

resProblem "col052" [(pr 7 (all (X1\ (n ((response c (common_bird X1)) == (response X1 (common_bird X1)))))) ),
(pr 5 (n (c == (compose a b))) ),
(pr 4 (all (X1\ (all (X2\ (all (X3\ (n ((response (compose X1 X2) X3) == (response X1 (response X2 X3)))))))))) ),
(pr 2 (all (X1\ (p ((response a X1) == (response odd_bird X1))))) )] 
(resteps [pm (id (idx 4)) (id (idx 5)) 3, pm (id (idx 2)) (id (idx 3)) 1, pm (id (idx 4)) (id (idx 7)) 6, pm (id (idx 1)) (id (idx 6)) 0])
 (map [
pr 7 (all (X1\ (n ((response c (common_bird X1)) == (response X1 (common_bird X1)))))),
pr 4 (all (X1\ (all (X2\ (all (X3\ (n ((response (compose X1 X2) X3) == (response X1 (response X2 X3)))))))))),
pr 6 (all (X1\ (all (X2\ (n ((response c (common_bird (compose X1 X2))) == (response X1 (response X2 (common_bird (compose X1 X2)))))))))),
pr 0 f-,
pr 1 (all (X1\ (p ((response c X1) == (response odd_bird (response b X1)))))),
pr 2 (all (X1\ (p ((response a X1) == (response odd_bird X1))))),
pr 5 (n (c == (compose a b))),
pr 3 (all (X1\ (n ((response c X1) == (response a (response b X1))))))
]).

inSig response.
inSig compose.
inSig common_bird.


