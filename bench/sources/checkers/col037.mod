module col037.

accumulate lkf-kernel.
accumulate eprover.
accumulate resolution_steps.

resProblem "col037" [(pr 12 (all (X1\ (all (X2\ (all (X3\ (n ((apply (apply (apply b X1) X2) X3) == (apply X1 (apply X2 X3)))))))))) ),
(pr 9 (all (X1\ (all (X2\ (all (X3\ (n ((apply (apply (apply s X1) X2) X3) == (apply (apply X1 X3) (apply X2 X3)))))))))) ),
(pr 6 (all (X1\ (all (X2\ (all (X3\ (n ((apply (apply (apply c X1) X2) X3) == (apply (apply X1 X3) X2))))))))) ),
(pr 4 (all (X1\ (p ((apply X1 (f X1)) == (apply (f X1) (apply X1 (f X1))))))) )] 
(resteps [pm (id (idx 6)) (id (idx 9)) 8, pm (id (idx 6)) (id (idx 8)) 7, pm (id (idx 6)) (id (idx 7)) 5, pm (id (idx 4)) (id (idx 5)) 3, pm (id (idx 12)) (id (idx 9)) 11, pm (id (idx 11)) (id (idx 6)) 10, pm (id (idx 3)) (id (idx 10)) 2, pm (id (idx 6)) (id (idx 9)) 8, pm (id (idx 6)) (id (idx 8)) 7, pm (id (idx 6)) (id (idx 7)) 5, pm (id (idx 2)) (id (idx 5)) 1, pm (id (idx 6)) (id (idx 9)) 8, pm (id (idx 6)) (id (idx 8)) 7, pm (id (idx 6)) (id (idx 7)) 5, pm (id (idx 6)) (id (idx 5)) 13, pm (id (idx 1)) (id (idx 13)) 0])
 (map [
pr 6 (all (X1\ (all (X2\ (all (X3\ (n ((apply (apply (apply c X1) X2) X3) == (apply (apply X1 X3) X2))))))))),
pr 1 (all (X1\ (p ((apply (apply (apply (apply s (apply c c)) c) X1) (f (apply X1 X1))) == (apply (apply (apply (apply s b) (apply c (apply (apply s (apply c c)) c))) (f (apply X1 X1))) X1))))),
pr 5 (all (X1\ (all (X2\ (n ((apply (apply (apply (apply s (apply c c)) c) X1) X2) == (apply (apply X1 X1) X2))))))),
pr 9 (all (X1\ (all (X2\ (all (X3\ (n ((apply (apply (apply s X1) X2) X3) == (apply (apply X1 X3) (apply X2 X3)))))))))),
pr 12 (all (X1\ (all (X2\ (all (X3\ (n ((apply (apply (apply b X1) X2) X3) == (apply X1 (apply X2 X3)))))))))),
pr 0 f-,
pr 13 (all (X1\ (all (X2\ (n ((apply (apply (apply (apply s (apply c c)) c) (apply c X1)) X2) == (apply (apply X1 X2) (apply c X1)))))))),
pr 10 (all (X2\ (all (X1\ (all (X3\ (n ((apply X2 (apply (apply X1 X3) X2)) == (apply (apply (apply (apply s b) (apply c X1)) X2) X3))))))))),
pr 3 (all (X1\ (p ((apply (f (apply X1 X1)) (apply (apply (apply (apply s (apply c c)) c) X1) (f (apply X1 X1)))) == (apply (apply X1 X1) (f (apply X1 X1))))))),
pr 2 (all (X1\ (p ((apply (apply (apply (apply s b) (apply c (apply (apply s (apply c c)) c))) (f (apply X1 X1))) X1) == (apply (apply X1 X1) (f (apply X1 X1))))))),
pr 4 (all (X1\ (p ((apply X1 (f X1)) == (apply (f X1) (apply X1 (f X1))))))),
pr 7 (all (X1\ (all (X2\ (all (X3\ (n ((apply (apply (apply (apply s (apply c c)) X1) X2) X3) == (apply (apply (apply X1 X2) X3) X2))))))))),
pr 11 (all (X2\ (all (X1\ (all (X3\ (n ((apply (apply (apply (apply s b) X2) X1) X3) == (apply X1 (apply (apply X2 X1) X3)))))))))),
pr 8 (all (X1\ (all (X3\ (all (X2\ (n ((apply (apply (apply s (apply c X1)) X3) X2) == (apply (apply X1 (apply X3 X2)) X2)))))))))
]).

inSig apply.
inSig f.


