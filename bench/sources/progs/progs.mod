module progs.

accumulate eval_examples.

main :- eval (app (abs f\ (abs x\ (abs y\ (app (app f x) y)))) (abs u\ (abs v\ u))) R1,
        eval (app (abs f\ (app (app f (abs x\ x)) (abs x\ (abs y\ y)))) (abs u\ (abs v\ u))) R2,
        eval (app (abs f\ (app (app f (abs x\ x)) (abs x\ (abs y\ y)))) (abs u\ (abs v\ v))) R3,
        eval (eq (c 5) (c 5)) R4,
        eval (lss (c 5) (c 3)) R5,
        eval (lss (c 3) (c 5)) R6,
        test 1 F1,
        test 2 F2,
        test 3 F3,
        test 4 F4,
        test 5 F5.
 
