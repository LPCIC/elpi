module progs1.

accumulate eval_examples.

main1 :- 
        %--- script1 ---
        eval (app (abs f\ (abs x\ (abs y\ (app (app f x) y)))) (abs u\ (abs v\ u))) R1,
        R1 = abs (x1\ abs (x2\ app (app (abs (x3\ abs (x4\ x3))) x1) x2)),

        eval (app (abs f\ (app (app f (abs x\ x)) (abs x\ (abs y\ y)))) (abs u\ (abs v\ u))) R2,
        R2 = abs (x1\ x1),
        
        eval (app (abs f\ (app (app f (abs x\ x)) (abs x\ (abs y\ y)))) (abs u\ (abs v\ v))) R3,
        R3 = abs (x1\ abs (x2\ x2)),

        eval (eq (c 5) (c 0)) R4, R4 = false,

        eval (eq (c 5) (c 0)) R5, R5 = false,
    
        eval (eq (c 5) (c 5)) R6, R6 = truth,

        eval (lss (c 5) (c 3)) R7, R7 = false,
  
        eval (lss (c 3) (c 5)) R8, R8 = truth,

        test 1 F1, F1 = c 120,

        test 2 F2, F2 = c 1,

        test 3 F3, F3 = c 5,

        test 4 F4, F4 = c 3,

        test 5 F5, F5 = cons (c 1) (cons (c 2) (cons (c 3) (cons (c 4) null))).

%    test 1 F6, F6 = fix (x1\ abs (x2\ abs (x3\ _ x2 x3 truth (x4\ x5\ app (app x1 x4) x5)))).
 
