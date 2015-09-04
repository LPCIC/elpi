/*
 * A testing harness for the interpreter (written in Lambda Prolog) for 
 * the functional programming language under consideration
 */

module  eval_examples. 

accumulate  eval, terms.

type  test   int -> tm -> o.

test 1 FactOf5 :-  trm trfact1 F, eval (app (app F (c 5)) (c 1)) FactOf5.

test 2 Gcd :- trm gcd2 F, eval (app (app F (c 5)) (c 1)) Gcd.

test 3 Gcd :- trm gcd2 F, eval (app (app F (c 5)) (c 35)) Gcd.

test 4 Gcd :- trm gcd2 F, eval (app (app F (c 33)) (c 9)) Gcd.

test 5 App :- trm appnd F, eval (app (app F (cons (c 1) (cons (c 2) null))) 
                                            (cons (c 3) (cons (c 4) null)))
                                App.
